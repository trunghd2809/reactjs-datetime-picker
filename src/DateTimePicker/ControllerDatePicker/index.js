import React, { useMemo } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import {
  faAngleDoubleLeft,
  faAngleLeft,
  faAngleDoubleRight,
  faAngleRight
} from '@fortawesome/free-solid-svg-icons'
import WeekDays from '../WeekDays'
import Days from '../Days'
import PropTypes from 'prop-types'
import styles from './styles.module.css'
import TimePicker from '../TimePicker'

const setupFormats = (locale) => {
  const date = new Date(1970, 2, 1)
  const dayFormat = new Intl.DateTimeFormat(locale, {
    weekday: 'short'
  })
  const monthFormat = new Intl.DateTimeFormat(locale, {
    month: 'long'
  })
  const weekdays = []
  const months = []
  for (let i = 2; i < 9; i++) {
    date.setDate(i)
    weekdays.push(dayFormat.format(date))
  }
  for (let i = 0; i < 12; i++) {
    date.setMonth(i)
    months.push(monthFormat.format(date))
  }
  return {
    weekdays,
    months
  }
}
const ControllerDatePicker = (props) => {
  const { weekdays, months } = useMemo(() => setupFormats('en-US'), [])
  const withprops = () => {
    const {
      value,
      active,
      setMonth,
      selectedMonth,
      onSelect,
      timePicker
    } = props
    const date = new Date(selectedMonth || value)
    const year = date.getFullYear()
    const month = date.getMonth()
    return {
      selectedMonth: new Date(year, month, 1),
      year,
      month,
      active,
      setMonth,
      onSelect,
      timePicker
    }
  }
  const {
    selectedMonth,
    year,
    month,
    active,
    setMonth,
    onSelect,
    timePicker
  } = withprops()
  const prev = () => {
    const year = selectedMonth.getFullYear()
    const month = selectedMonth.getMonth()
    setMonth(new Date(year, month - 1, 1, 0, 0, 0, 0))
  }
  const next = () => {
    const year = selectedMonth.getFullYear()
    const month = selectedMonth.getMonth()
    setMonth(new Date(year, month + 1, 1, 0, 0, 0, 0))
  }
  const prevYear = () => {
    const year = selectedMonth.getFullYear()
    const month = selectedMonth.getMonth()
    setMonth(new Date(year, month - 12, 1, 0, 0, 0, 0))
  }
  const nextYear = () => {
    const year = selectedMonth.getFullYear()
    const month = selectedMonth.getMonth()
    setMonth(new Date(year, month + 12, 1, 0, 0, 0, 0))
  }
  return (
    <div className={styles.pickerWrapper}>
      <React.Fragment>
        <div className={styles.controls}>
          <div className={styles.buttonGroupLeft}>
            <a className={styles.button}>
              <FontAwesomeIcon icon={faAngleDoubleLeft} onClick={prevYear} />
            </a>
            <a className={styles.button} onClick={prev}>
              <FontAwesomeIcon icon={faAngleLeft} />
            </a>
          </div>
          <div className={styles.header}>
            {months[month]} - {year}
          </div>
          <div className={styles.buttonGroupRight}>
            <a className={styles.button}>
              <FontAwesomeIcon icon={faAngleRight} onClick={next} />
            </a>
            <a className={styles.button}>
              <FontAwesomeIcon icon={faAngleDoubleRight} onClick={nextYear} />
            </a>
          </div>
        </div>
        <WeekDays weekdays={weekdays} />
        <Days
          year={year}
          month={month}
          active={active}
          onChange={onSelect}
          value={props.value}
        />
      </React.Fragment>
      {timePicker && <TimePicker value={props.value} onChange={onSelect} />}
    </div>
  )
}

ControllerDatePicker.propTypes = {
  value: PropTypes.instanceOf(Date),
  selectedMonth: PropTypes.instanceOf(Date),
  setMonth: PropTypes.func,
  active: PropTypes.func,
  onSelect: PropTypes.func,
  timePicker: PropTypes.bool
}

export default ControllerDatePicker
