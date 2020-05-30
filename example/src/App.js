import React, { useState } from 'react'

import { DateTimePicker } from 'reactjs-datetime-picker'
import 'reactjs-datetime-picker/dist/index.css'

const App = () => {
  const [value, setValue] = useState(new Date())
  return (
    <div style={{ 
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      alignSelf: 'center',
      height: '100vh',
    }}>
      <DateTimePicker placeholder="Select date" value={value} onChange={(value) => setValue(value)} timePicker/>
    </div>
  )
}

export default App
