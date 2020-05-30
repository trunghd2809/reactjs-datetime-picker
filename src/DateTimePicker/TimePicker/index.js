/* eslint-disable prettier/prettier */
import React from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faClock } from '@fortawesome/free-solid-svg-icons'
import PropTypes from 'prop-types'
import DropDown from '../Dropdown';
import styles from './styles.module.css'

const hours = [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23
  ].map((hour) => ({
    value: hour,
    key: hour,
    text: hour,
  }));
const minutes = [0, 15, 30, 45].map((minute) => ({
  value: minute,
  key: minute,
  text: minute,
}));
const TimePicker = (props) => {
  const withProps = () => {
    const { value } = props;
    if (!value) return { hour: 0, minute: 0 }
    const date = new Date(value);
    const hour = date.getHours();
    const minute = Math.round(date.getMinutes() / 15) * 15;
    return { hour, minute };
  }
  const onSelectHours = (hours) => {
    const date = new Date(props.value)
    date.setHours(hours, date.getMinutes(), 0)
    if (typeof props.onChange === 'function') props.onChange(date)
  }
  const onSelectMinute = (minutes) => {
    const date = new Date(props.value)
    date.setHours(date.getHours(), minutes, 0)
    if (typeof props.onChange === 'function') props.onChange(date)
  }
  const { hour, minute } = withProps()
  return (
    <div className={styles.timePicker}>
      <div className={styles.label}>
        <FontAwesomeIcon icon={faClock} />
      </div>
      <div className={styles.hour}>
        <DropDown options={hours} value={hour} onChange={onSelectHours} />
      </div>
      <div className={styles.minute}>
        <DropDown options={minutes} value={minute} onChange={onSelectMinute}/>
      </div>
    </div>
  )
}

TimePicker.propTypes = {
  value: PropTypes.instanceOf(Date),
  onChange: PropTypes.func
}

export default React.memo(TimePicker)
