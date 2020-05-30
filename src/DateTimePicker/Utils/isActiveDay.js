export default (date1, date2) => {
  const left = date1 instanceof Date ? date1 : new Date(date1)
  const right = date2 instanceof Date ? date2 : new Date(date2)
  return (
    left.getFullYear() === right.getFullYear() &&
    left.getMonth() === right.getMonth() &&
    left.getDate() === right.getDate()
  )
}
