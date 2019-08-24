use crate::{Field, Curve};

// TODO: This is not secure yet.
pub struct Transcript<C: Curve> {
    cur: C::Base,
}

impl<C: Curve> Transcript<C> {
    pub fn new() -> Self {
        Transcript {
            cur: <C::Base as Field>::ALPHA,
        }
    }

    pub fn append_scalar(&mut self, e: C::Scalar) {
        // TODO: the entire scalar needs to be hashed
        let ours: C::Base = e.get_lower_128();
        self.append_base(ours);
    }

    pub fn append_base(&mut self, base: C::Base) {
        let tmp = self.cur + base;
        self.cur = tmp.square();
    }

    pub fn append_point(&mut self, point: &C) {
        let (x, y) = point.get_xy();
        self.append_base(x);
        self.append_base(y);
    }

    pub fn append_groth_commitment(&mut self, comm: &crate::commitment::GrothCommitment<C>) {
        for p in comm.get_points() {
            self.append_point(p);
        }
    }

    pub fn get_challenge<FF: Field>(&mut self) -> FF {
        let tmp = self.cur;
        self.cur = self.cur * self.cur.square();

        tmp.get_lower_128()
    }
}
