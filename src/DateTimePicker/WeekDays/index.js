import React from 'react'
import styles from './styles.module.css'
import PropTypes from 'prop-types'

const WeekDays = ({ weekdays }) => {
  return (
    <div className={styles.week}>
      {weekdays.map((day) => (
        <div key={day} className={styles.weekDay}>
          {day}
        </div>
      ))}
    </div>
  )
}

WeekDays.propTypes = {
  weekdays: PropTypes.array
}

export default React.memo(WeekDays)
