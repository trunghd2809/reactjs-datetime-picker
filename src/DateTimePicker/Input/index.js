import React from 'react'
import PropTypes from 'prop-types'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faCalendar } from '@fortawesome/free-solid-svg-icons'
import DatePicker from '../DatePicker'
import styles from './styles.module.css'

const format = (date, timePicker) => {
  const year = date.getFullYear()
  const month = date.getMonth()
  const day = date.getDate()
  const hour = `0${date.getHours()}`.slice(-2)
  const minute = `0${date.getMinutes()}`.slice(-2)
  return timePicker
    ? `${month}/${day}/${year}, ${hour}:${minute}`
    : `${month}/${day}/${year}`
}
const Input = (props) => {
  const { placeholder, value, timePicker } = props
  const onChange = (date) => {
    if (typeof props.onChange === 'function') props.onChange(date)
  }
  const label = timePicker ? format(value, true) : format(value, false)
  return (
    <div className={styles.InputWrapper}>
      <input placeholder={placeholder} value={label} readOnly />
      <div className={styles.svgWrapper}>
        <FontAwesomeIcon icon={faCalendar} />
      </div>
      <div className={styles.PopUpWrapper}>
        <DatePicker value={value} onSelect={onChange} timePicker={timePicker} />
      </div>
    </div>
  )
}
export default React.memo(Input)
Input.propTypes = {
  value: PropTypes.instanceOf(Date).isRequired,
  placeholder: PropTypes.string,
  onChange: PropTypes.func,
  timePicker: PropTypes.bool
}
Input.defautProps = {
  timePicker: false
}
