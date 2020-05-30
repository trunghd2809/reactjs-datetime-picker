/* eslint-disable no-unused-vars */
import React, { useState } from 'react'
import PropTypes from 'prop-types'
import ControllerDatePicker from '../ControllerDatePicker'
import isActiveDay from '../Utils/isActiveDay'
const DatePicker = (props) => {
  const [selectedMonth, setMonth] = useState(() => {
    return new Date(props.value)
  })
  const active = (date) => {
    return isActiveDay(date, props.value)
  }
  return (
    <ControllerDatePicker
      value={props.value}
      selectedMonth={selectedMonth}
      setMonth={setMonth}
      active={active}
      onSelect={props.onSelect}
      timePicker={props.timePicker}
    />
  )
}
export default React.memo(DatePicker)
DatePicker.propTypes = {
  value: PropTypes.instanceOf(Date).isRequired,
  onSelect: PropTypes.func,
  timePicker: PropTypes.bool
}