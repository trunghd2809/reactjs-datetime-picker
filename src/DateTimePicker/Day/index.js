import React from 'react'
import cx from 'classnames'
import styles from './styles.module.css'
import PropTypes from 'prop-types'

const Day = ({ monthDay, active, onChange, date }) => {
  const className = cx(styles.day, {
    [styles.active]: active
  })
  const onClick = (e) => {
    e.preventDefault()
    if (typeof onChange === 'function') onChange(date)
  }
  return (
    <div onClick={onClick} className={className}>
      {monthDay}
    </div>
  )
}

Day.propTypes = {
  onChange: PropTypes.func
}

export default Day
