import React, { useState } from 'react'
import PropTypes from 'prop-types'
import cx from 'classnames'
import styles from './styles.module.css'

const DropDown = (props) => {
  const [open, setOpen] = useState(false)
  const className = cx(styles.dropDown, {
    [styles.open]: open
  })
  const { options, onChange } = props
  const onClick = (option) => {
    if (typeof onChange === 'function') onChange(option.value)
  }
  return (
    <div className={className} onClick={() => setOpen(!open)}>
      <div className={styles.body}>
        <div className={styles.displayWrapper}>
          <div className={styles.display}>
            <input
              type='text'
              readOnly
              className={styles.fakeInput}
              value={props.value}
            />
          </div>
          <div className={styles.menu}>
            <ul>
              {options.map((option) => {
                return (
                  <li key={option.key}>
                    <a onClick={() => onClick(option)}>{option.text}</a>
                  </li>
                )
              })}
            </ul>
          </div>
        </div>
      </div>
    </div>
  )
}

DropDown.propTypes = {
  options: PropTypes.array,
  onChange: PropTypes.func
}

export default React.memo(DropDown)
