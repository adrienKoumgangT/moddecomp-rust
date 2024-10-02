

pub mod calcul_stat {
    use std::time::Instant;

    pub fn measure_time<F, R>(func: F) -> (u128, R)
    where
        F: FnOnce() -> R,
    {
        let start = Instant::now();
        let result = func();
        let duration = start.elapsed().as_micros();
        (duration, result)
    }

    // The closure takes parameters of type `P` and returns a result of type `R`.
    pub fn measure_time_with_param<F, R, P>(func: F, param: P) -> (u128, R)
    where
        F: FnOnce(P) -> R,
    {
        let start = Instant::now();
        let result = func(param);
        let duration = start.elapsed().as_micros();
        (duration, result)
    }
}
