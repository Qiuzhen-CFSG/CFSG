module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Coefficients

/-!
# Sparse supports of the signed short-root coefficients

Each binary divided-power row contains at most two nonzero entries. These
explicit supports describe both root signs, with root reversal for the negative
curves. Kernel reduction checks each support against the coefficient table;
subsequent arguments can sum only the displayed coordinates.
-/

@[expose] public section

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
namespace Coefficients

def reverseCoordinates : Index → Index := Sum.map id Fin.rev

def rowSupport (s k : Bool) (n : Fin 3) (r : Index) : Finset Index :=
  match s, k with
  | false, false => match n.val, (finSumFinEquiv r).val with
    | 0, 3 => {Sum.inr 33}
    | 0, 7 => {Sum.inr 7}
    | 0, 12 => {Sum.inr 15}
    | 0, 13 => {Sum.inr 16}
    | 0, 14 => {Sum.inr 17}
    | 0, 15 => {Sum.inr 20}
    | 0, 16 => {Sum.inr 21}
    | 0, 17 => {Sum.inr 23}
    | 0, 18 => {Sum.inl 2}
    | 0, 28 => {Sum.inr 34}
    | 0, 30 => {Sum.inr 35}
    | 0, 34 => {Sum.inr 37}
    | 0, 40 => {Sum.inr 41}
    | 0, 42 => {Sum.inr 42}
    | 0, 43 => {Sum.inr 43}
    | 0, 44 => {Sum.inr 44}
    | 1, 8 => {Sum.inr 15}
    | 1, 9 => {Sum.inr 16}
    | 1, 10 => {Sum.inr 20}
    | 1, 18 => {Sum.inr 33}
    | 1, 31 => {Sum.inr 41}
    | 1, 35 => {Sum.inr 42}
    | 1, 36 => {Sum.inr 43}
    | _, _ => ∅
  | false, true => match n.val, (finSumFinEquiv r).val with
    | 0, 2 => {Sum.inr 24}
    | 0, 7 => {Sum.inr 4}
    | 0, 11 => {Sum.inr 8}
    | 0, 13 => {Sum.inr 10}
    | 0, 15 => {Sum.inr 12}
    | 0, 17 => {Sum.inr 14}
    | 0, 21 => {Sum.inr 18}
    | 0, 25 => {Sum.inr 22}
    | 0, 27 => {Sum.inl 1, Sum.inl 3}
    | 0, 30 => {Sum.inr 27}
    | 0, 34 => {Sum.inr 31}
    | 0, 37 => {Sum.inr 34}
    | 0, 39 => {Sum.inr 36}
    | 0, 41 => {Sum.inr 38}
    | 0, 43 => {Sum.inr 40}
    | 0, 48 => {Sum.inr 45}
    | 1, 6 => {Sum.inr 4}
    | 1, 20 => {Sum.inr 18}
    | 1, 24 => {Sum.inr 22}
    | 1, 27 => {Sum.inr 24}
    | 1, 29 => {Sum.inr 27}
    | 1, 33 => {Sum.inr 31}
    | 1, 47 => {Sum.inr 45}
    | _, _ => ∅
  | true, false => match n.val, (finSumFinEquiv r).val with
    | 0, 3 => {Sum.inr 14}
    | 0, 11 => {Sum.inr 3}
    | 0, 12 => {Sum.inr 4}
    | 0, 13 => {Sum.inr 5}
    | 0, 15 => {Sum.inr 6}
    | 0, 21 => {Sum.inr 10}
    | 0, 25 => {Sum.inr 12}
    | 0, 27 => {Sum.inr 13}
    | 0, 37 => {Sum.inl 2}
    | 0, 38 => {Sum.inr 24}
    | 0, 39 => {Sum.inr 26}
    | 0, 40 => {Sum.inr 27}
    | 0, 41 => {Sum.inr 30}
    | 0, 42 => {Sum.inr 31}
    | 0, 43 => {Sum.inr 32}
    | 0, 48 => {Sum.inr 40}
    | 1, 19 => {Sum.inr 4}
    | 1, 20 => {Sum.inr 5}
    | 1, 24 => {Sum.inr 6}
    | 1, 37 => {Sum.inr 14}
    | 1, 45 => {Sum.inr 27}
    | 1, 46 => {Sum.inr 31}
    | 1, 47 => {Sum.inr 32}
    | _, _ => ∅
  | true, true => match n.val, (finSumFinEquiv r).val with
    | 0, 2 => {Sum.inr 23}
    | 0, 7 => {Sum.inr 2}
    | 0, 12 => {Sum.inr 7}
    | 0, 14 => {Sum.inr 9}
    | 0, 16 => {Sum.inr 11}
    | 0, 18 => {Sum.inr 13}
    | 0, 21 => {Sum.inr 16}
    | 0, 25 => {Sum.inr 20}
    | 0, 28 => {Sum.inl 1, Sum.inl 3}
    | 0, 30 => {Sum.inr 25}
    | 0, 34 => {Sum.inr 29}
    | 0, 38 => {Sum.inr 33}
    | 0, 40 => {Sum.inr 35}
    | 0, 42 => {Sum.inr 37}
    | 0, 44 => {Sum.inr 39}
    | 0, 48 => {Sum.inr 43}
    | 1, 8 => {Sum.inr 2}
    | 1, 22 => {Sum.inr 16}
    | 1, 26 => {Sum.inr 20}
    | 1, 28 => {Sum.inr 23}
    | 1, 31 => {Sum.inr 25}
    | 1, 35 => {Sum.inr 29}
    | 1, 49 => {Sum.inr 43}
    | _, _ => ∅

theorem coefficient_support : ∀ (s k : Bool) (n : Fin 3) (r c : Index),
    (if s then coefficient k n r c else
      coefficient k n (reverseCoordinates r) (reverseCoordinates c)) =
      if c ∈ rowSupport s k n r then 1 else 0 := by
  let dec : Decidable (∀ (s k : Bool) (n : Fin 3) (r c : Index),
      (if s then coefficient k n r c else
        coefficient k n (reverseCoordinates r) (reverseCoordinates c)) =
        if c ∈ rowSupport s k n r then 1 else 0) :=
    @Fintype.decidableForallFintype Bool _ (fun s =>
      @Fintype.decidableForallFintype Bool _ (fun k =>
        @Fintype.decidableForallFintype (Fin 3) _ (fun n =>
          @Fintype.decidableForallFintype Index _ (fun r =>
            @Fintype.decidableForallFintype Index _
              (fun c => ZMod.decidableEq 2 _ _) inferInstance) inferInstance) inferInstance)
          inferInstance) inferInstance
  exact @of_decide_eq_true _ dec (by decide +kernel)

end Coefficients
end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
