# reactjs-datetime-picker
  A simple and reusable Datepicker component for React
  <img width="396" alt="Screen Shot 2020-05-30 at 16 02 41" src="https://user-images.githubusercontent.com/38755997/83325314-a4630100-a295-11ea-8710-66e93a6e91f4.png">

> React js DateTime Picker

[![NPM](https://img.shields.io/npm/v/reactjs-datetime-picker.svg)](https://www.npmjs.com/package/reactjs-datetime-picker) [![JavaScript Style Guide](https://img.shields.io/badge/code_style-standard-brightgreen.svg)](https://standardjs.com)

## Install

```bash
npm i datetime-picker-reactjs
```

## Usage

```jsx
import React, { Component } from 'react'

import { DateTimePicker } from 'datetime-picker-reactjs'
import 'datetime-picker-reactjs/dist/index.css'

class Example extends Component {
  render() {
    return <DateTimePicker value={new Date()}/>
  }
}
```

## License

MIT © [trunghd2809](https://github.com/trunghd2809)
