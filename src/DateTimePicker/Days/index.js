import React from 'react'
import cx from 'classnames'
import PropTypes from 'prop-types'
import styles from './styles.module.css'
import Day from '../Day'

const days = [0, 1, 2, 3, 4, 5, 6]
const weeks = [0, 1, 2, 3, 4, 5]
const emptyDay = cx(styles.day, styles.empty)

const Days = (props) => {
  const withProps = () => {
    const { year, month, active } = props
    const firstOfMonth = new Date(year, month, 1)
    const lastOfMonth = new Date(year, month + 1, 0)
    const start = firstOfMonth.getUTCDay()
    const end = start + lastOfMonth.getDate() - 1
    return {
      year,
      month,
      start,
      end,
      active
    }
  }
  const onChange = (date) => {
    const newDate = new Date(date)
    const newValue = new Date(props.value)
    newDate.setHours(newValue.getHours(), newValue.getMinutes())
    if (typeof props.onChange === 'function') props.onChange(newDate)
  }

  const { year, month, start, end, active } = withProps()
  return (
    <div className={styles.month}>
      {weeks.map((week) => {
        return (
          <div className={styles.week} key={`${year}-${month}-${week}`}>
            {days.map((weekDay) => {
              const count = week * 7 + weekDay
              const monthDay = count - start + 1
              const dayDate = new Date(year, month, monthDay, 0, 0, 0, 0)
              if (count >= start && count <= end) {
                return (
                  <Day
                    monthDay={monthDay}
                    date={dayDate}
                    key={weekDay}
                    active={active(dayDate)}
                    onChange={onChange}
                  />
                )
              }
              return <div key={weekDay} className={emptyDay} />
            })}
          </div>
        )
      })}
    </div>
  )
}

Days.propTypes = {
  year: PropTypes.number,
  month: PropTypes.number,
  active: PropTypes.func,
  onChange: PropTypes.func,
  value: PropTypes.instanceOf(Date)
}

export default React.memo(Days)
