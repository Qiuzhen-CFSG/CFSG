module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.PGroupCore

/-!
# The seven-action obstruction in the covered case

The action on `X/O₂(X)` has image of order prime to seven. In its kernel,
the action on `O₂(X)/Φ(O₂(X))` lies in the module centralizer, also of order
prime to seven. An index calculation combines these two bounds. Burnside's
Frattini-kernel theorem lifts the bound to the action on `O₂(X)`.
Consequently `O^{7′}(M)` centralizes that two-core. If `V = Φ(O₂(X))`, it
centralizes `V`, contradicting an action image of order 21 on `V`.

Only absence of seven in the two action images is needed; a classification
of the complete endomorphism ring is unnecessary. The intrinsic model
bounds remain explicit. This proves the deduction from those bounds, not
those bounds for the `G₂(4)` cover.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed p.1202. Residual means `O^{7′}`, never `O₇`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
open Subgroup

/-- Combine the quotient image with the image of its kernel. The two actions
need not factor through one another. -/
theorem seven_coprime_range_of_kernel
    {M H B : Type*} [Group M] [Group H] [Group B]
    (q : M →* H) (a : M →* B)
    (hq : Nat.Coprime 7 (Nat.card q.range))
    (hk : Nat.Coprime 7 (Nat.card (q.ker.map a))) :
    Nat.Coprime 7 (Nat.card a.range) := by
  have hc : Nat.Coprime 7 (a.ker ⊓ q.ker).index := by
    rw [← relIndex_mul_index (show a.ker ⊓ q.ker ≤ q.ker from inf_le_right),
      inf_relIndex_right, relIndex_ker, index_ker]
    exact hk.mul_right hq
  rw [← index_ker]
  exact hc.coprime_dvd_right (index_dvd_of_le inf_le_left)

/-- A two-group automorphism kernel cannot introduce seven into the image. -/
theorem seven_coprime_frattini_lift
    {M Q : Type*} [Group M] [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (a : M →* MulAut Q)
    (hΦ : Nat.Coprime 7 (Nat.card ((quotientAut (frattini Q)).comp a).range)) :
    Nat.Coprime 7 (Nat.card a.range) := by
  let f := quotientAut (frattini Q)
  let r : a.range →* MulAut (Q ⧸ frattini Q) := f.comp a.range.subtype
  have hk : IsPGroup 2 r.ker :=
    (isPGroup_quotientAut_frattini_kernel hQ).comap_of_injective
      a.range.subtype a.range.subtype_injective
  obtain ⟨n, hn⟩ := hk.exists_card_dvd_pow
  have hc : Nat.Coprime 7 (Nat.card r.ker) :=
    ((by decide : Nat.Coprime 7 2).pow_right n).coprime_dvd_right hn
  have he : r.range = (f.comp a).range := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨m, hm⟩ := u.property
      exact ⟨m, congrArg f hm⟩
    · rintro ⟨m, rfl⟩
      exact ⟨⟨a m, ⟨m, rfl⟩⟩, rfl⟩
  have hr : Nat.Coprime 7 (Nat.card r.range) := he ▸ hΦ
  rw [← r.ker.card_mul_index, index_ker]
  exact hc.mul_right hr

/-- The actual actions on the two sections used on p.1202. -/
def coreAction {M X : Type*} [Group M] [Group X] (a : M →* MulAut X) :
    M →* MulAut (pCore 2 X) :=
  (MulAut.characteristic (pCore 2 X)).comp a

def topAction {M X : Type*} [Group M] [Group X] (a : M →* MulAut X) :
    M →* MulAut (X ⧸ pCore 2 X) :=
  (quotientAut (pCore 2 X)).comp a

def sectionAction {M X : Type*} [Group M] [Group X] (a : M →* MulAut X) :
    M →* MulAut (pCore 2 X ⧸ frattini (pCore 2 X)) :=
  (quotientAut (frattini (pCore 2 X))).comp (coreAction a)

/-- The two intrinsic image bounds imply that the whole two-core action has
order prime to seven. The second premise only concerns actors fixing `X/O₂(X)`. -/
theorem seven_coprime_coreAction
    {M X : Type*} [Group M] [Group X] [Finite X]
    (a : M →* MulAut X)
    (hquot : Nat.Coprime 7 (Nat.card (topAction a).range))
    (hmodule : Nat.Coprime 7
      (Nat.card ((topAction a).ker.map (sectionAction a)))) :
    Nat.Coprime 7 (Nat.card (coreAction a).range) := by
  apply seven_coprime_frattini_lift pCore_isPGroup
  exact seven_coprime_range_of_kernel (topAction a) (sectionAction a) hquot hmodule

/-- Thus the source residual centralizes the actual two-core. -/
theorem primeToResidual_le_coreAction_kernel
    {M X : Type*} [Group M] [Group X] [Finite X]
    (a : M →* MulAut X)
    (hquot : Nat.Coprime 7 (Nat.card (topAction a).range))
    (hmodule : Nat.Coprime 7
      (Nat.card ((topAction a).ker.map (sectionAction a)))) :
    primeToResidual 7 M ≤ (coreAction a).ker := by
  have h := primeToResidual_le_ker (coreAction a).rangeRestrict
    (seven_coprime_coreAction a hquot hmodule)
  rwa [MonoidHom.ker_rangeRestrict] at h

/-- A seven-divisible image must detect the prime-to-seven residual.
No assertion that the residual itself is a seven-group is used. -/
theorem exists_residual_mover
    {M B : Type*} [Group M] [Finite M] [Group B]
    (b : M →* B) (hseven : 7 ∣ Nat.card b.range) :
    ∃ y : primeToResidual 7 M, b y ≠ 1 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  by_contra hn
  have hle : primeToResidual 7 M ≤ b.ker := by
    intro y hy
    apply MonoidHom.mem_ker.mpr
    by_contra hyb
    exact hn ⟨⟨y, hy⟩, hyb⟩
  have hc := (primeToResidual_index_coprime (G := M) 7).coprime_dvd_right
    (index_dvd_of_le hle)
  rw [index_ker] at hc
  exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mp hc hseven

/-- Apply the residual to `V ≤ O₂(X)`, with its actual compatible action.
The source supplies the stronger equality `V = Φ(O₂(X))`; containment is
all that the final contradiction needs. -/
theorem no_seven_image_on_core_subgroup
    {M X V : Type*} [Group M] [Finite M] [Group X] [Finite X] [Group V]
    (a : M →* MulAut X) (b : M →* MulAut V)
    (j : V →* pCore 2 X) (hj : Function.Injective j)
    (hcompat : ∀ m v, j (b m v) = coreAction a m (j v))
    (hquot : Nat.Coprime 7 (Nat.card (topAction a).range))
    (hmodule : Nat.Coprime 7
      (Nat.card ((topAction a).ker.map (sectionAction a))))
    (hseven : 7 ∣ Nat.card b.range) : False := by
  obtain ⟨y, hy⟩ := exists_residual_mover b hseven
  have hc : coreAction a y = 1 := MonoidHom.mem_ker.mp
    (primeToResidual_le_coreAction_kernel a hquot hmodule y.property)
  apply hy
  apply MulEquiv.ext
  intro v
  apply hj
  rw [hcompat, hc]
  rfl

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
