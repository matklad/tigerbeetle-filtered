function assert(condition) {
  if (!condition) {
    alert("Assertion failed");
    throw "Assertion failed";
  }
}

async function runs_fetch() {
  const DATA_URL =
    "https://raw.githubusercontent.com/matklad/gitdb/main/macro-benchmark/data.json";
  const data = await (await fetch(DATA_URL)).text();
  console.log(data);
  return data.split("\n")
    .filter((it) => it.length > 0)
    .map((it) => JSON.parse(it));
}

function runs_to_series(runs) {
  let result = new Map();
  for (const run of runs) {
    for (const measurement of run.measurements) {
      if (!result.has(measurement.label)) {
        result.set(measurement.label, {
          label: measurement.label,
          unit: undefined,
          value: [],
          revision: [],
          timestamp: [],
        });
      }
      const series = result.get(measurement.label);
      assert(series.label == measurement.label);

      if (series.unit) {
        assert(series.unit == measurement.unit);
      } else {
        series.unit = measurement.unit;
      }

      series.value.push(measurement.value);
      series.revision.push(run.revision);
      series.timestamp.push(run.timestamp);
    }
  }
  return result.values();
}

function series_display(series_list, root_node) {
  for (const series of series_list) {
    let options = {
      title: {
        text: series.label,
      },
      chart: {
        type: "bar",
        height: "400px",
      },
      series: [{
        name: series.label,
        data: series.timestamp.map((t, i) => [t * 1000, series.value[i]]),
      }],
      xaxis: {
        type: "datetime",
      },
    };
    if (series.unit === "bytes") {
      options = Object.assign(options, {
        yaxis: {
          labels: {
            formatter: formatBytes,
          },
        },
      });
    }
    if (series.unit === "ms") {
      options = Object.assign(options, {
        yaxis: {
          labels: {
            formatter: formatDuration,
          },
        },
      });
    }
    let div = document.createElement("div");
    root_node.append(div);
    var chart = new ApexCharts(div, options);
    chart.render();
  }
}

function formatBytes(bytes) {
  if (bytes === 0) return "0 Bytes";

  const k = 1024;
  const sizes = [
    "Bytes",
    "KiB",
    "MiB",
    "GiB",
    "TiB",
    "PiB",
    "EiB",
    "ZiB",
    "YiB",
  ];

  const i = Math.floor(Math.log(bytes) / Math.log(k));

  return parseFloat((bytes / Math.pow(k, i)).toFixed(2)) + " " + sizes[i];
}

function formatDuration(durationInSeconds) {
  const hours = Math.floor(durationInSeconds / 3600);
  const minutes = Math.floor((durationInSeconds % 3600) / 60);
  const seconds = durationInSeconds % 60;
  const milliseconds = Math.floor(
    (durationInSeconds - Math.floor(durationInSeconds)) * 1000,
  );
  const parts = [];

  if (hours > 0) {
    parts.push(`${hours}h`);
  }
  if (minutes > 0) {
    parts.push(`${minutes}m`);
  }
  if (seconds > 0 || parts.length === 0) {
    parts.push(`${seconds}s`);
  }
  if (milliseconds > 0) {
    parts.push(`${milliseconds}ms`);
  }

  return parts.join(" ");
}

function formatDuration(durationInMilliseconds) {
  const milliseconds = durationInMilliseconds % 1000;
  const seconds = Math.floor((durationInMilliseconds / 1000) % 60);
  const minutes = Math.floor((durationInMilliseconds / (1000 * 60)) % 60);
  const hours = Math.floor((durationInMilliseconds / (1000 * 60 * 60)) % 24);
  const days = Math.floor(durationInMilliseconds / (1000 * 60 * 60 * 24));
  const parts = [];

  if (days > 0) {
    parts.push(`${days}d`);
  }
  if (hours > 0) {
    parts.push(`${hours}h`);
  }
  if (minutes > 0) {
    parts.push(`${minutes}m`);
  }
  if (seconds > 0 || parts.length === 0) {
    parts.push(`${seconds}s`);
  }
  if (milliseconds > 0) {
    parts.push(`${milliseconds}ms`);
  }

  return parts.join(" ");
}

async function main() {
  const charts = document.querySelector("#charts");

  const runs = await runs_fetch();
  const series = runs_to_series(runs);
  series_display(series, charts);
}

window.onload = main;
