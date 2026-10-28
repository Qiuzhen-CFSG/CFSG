module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoCubicNormalizer

/-!
# Central fixation in the original Hall–Janko outer extension

Core preservation transports the concrete bound |Z(Q)| ≤ 4 to the
original second endpoint. On a set of at most four points, an involution
commuting with a cubic that fixes precisely the distinguished point acts
trivially. Applied to conjugation on Z(Q), this shows that the constructed
outer involution fixes every central core element. Its exact inversion
relation with the reduced cubic forces that cubic to fix Z(Q) as well.

Thus the source z-fixing relation is proved for any marked z in this
center. Placement of the chosen actors in the same original Borel and the
remaining endpoint-generator relations still have to be established.
No Aut(J₂) equivalence is asserted here.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–231,
especially the choice of x centralizing d and z on p.230.
The finite permutation check has at most four letters; the radical itself
is the unchanged original two-core, identified by the existing inclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo

private theorem four_permutation_check : ∀ n : Fin 5,
    ∀ a b : Equiv.Perm (Fin n.val), ∀ o,
    a o=o → b o=o → (∀ v, a (a (a v))=v) → (∀ v,b (b v)=v) →
    (∀ v,a (b v)=b (a v)) → (∀ v,a v=v → v=o) → ∀ v,b v=v := by
  intro n
  fin_cases n <;> decide +kernel

private theorem four_permutation_fixed {V : Type*} [Finite V]
    (hV : Nat.card V ≤ 4) (a b : Equiv.Perm V) (o : V)
    (hao : a o=o) (hbo : b o=o) (ha : ∀ v,a (a (a v))=v) (hb : ∀ v,b (b v)=v)
    (hab : ∀ v,a (b v)=b (a v)) (hfix : ∀ v,a v=v → v=o) : ∀ v,b v=v := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let n : Fin 5 := ⟨Fintype.card V,by rw [←Nat.card_eq_fintype_card]; omega⟩
  let e := Fintype.equivFin V
  let a' : Equiv.Perm (Fin n.val) := e.symm.trans (a.trans e)
  let b' : Equiv.Perm (Fin n.val) := e.symm.trans (b.trans e)
  have hh := four_permutation_check n a' b' (e o)
  have ha' : a' (e o)=e o := by simpa [a'] using congrArg e hao
  have hb' : b' (e o)=e o := by simpa [b'] using congrArg e hbo
  have ha3 : ∀ v,a' (a' (a' v))=v := by
    intro v
    simpa [a'] using congrArg e (ha (e.symm v))
  have hb2 : ∀ v,b' (b' v)=v := by
    intro v
    simpa [b'] using congrArg e (hb (e.symm v))
  have hab' : ∀ v,a' (b' v)=b' (a' v) := by
    intro v
    simpa [a',b'] using congrArg e (hab (e.symm v))
  have hf : ∀ v,a' v=v → v=e o := by
    intro v hv
    have h := congrArg e.symm hv
    have he : a (e.symm v)=e.symm v := by simpa [a'] using h
    simpa using congrArg e (hfix _ he)
  intro v
  have h := hh ha' hb' ha3 hb2 hab' hf (e v)
  exact e.injective (by simpa [b'] using h)

open SuzukiContainment GreenBook
open Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The center of the same original second core still has at most four elements. -/
theorem original_second_core_center_card_le (h : HypothesisF11 L S) (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1) :
    Nat.card (center (pCore 2 (parabolic L S j))) ≤ 4 := by
  let P := parabolic L S j
  let R := parabolic L (reducedSylow L S) j
  let eo := (pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective
  let er := (pCore 2 R).equivMapOfInjective R.subtype R.subtype_injective
  let v : pCore 2 P ≃* pCore 2 R := eo.trans
    ((MulEquiv.subgroupCongr (reduced_parabolic_core h j).symm).trans er.symm)
  let g := f.trans (MulEquiv.subgroupCongr HallJanko.j2Model_P_one)
  let w := (LocalCoreTransport.coreEquiv 2 g).trans
    ((MulEquiv.subgroupCongr (PairNormalizer.p₂_core_eq_q₂ SecondParabolic.l₂_core_card)).trans
      (subgroupOfEquivOfLe Seed.q₂.le_normalizer))
  have hc := Nat.card_congr (Subgroup.centerCongr (v.trans w)).toEquiv
  exact hc ▸ NormalizerAction.card_center_q₂_le

private def coreCenter (P : Subgroup G) : Subgroup P :=
  (center (pCore 2 P)).map (pCore 2 P).subtype

private instance coreCenter_normal (P : Subgroup G) : (coreCenter P).Normal :=
  ConjAct.normal_of_characteristic_of_normal

private def centerAction (P : Subgroup G) : P →* MulAut (coreCenter P) :=
  MulAut.conjNormal

/-- An involution commuting with the marked fixed-point-free cubic fixes the
whole center of the original second core. This is the z-fixing relation on
that center, without imposing it as an extra hypothesis. -/
theorem originalCubic_commuting_involution_fixes_core_center
    (h : HypothesisF11 L S) (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (x : parabolic L S j) (hx : x^2=1)
    (hax : originalCubic h j f*x=x*originalCubic h j f) :
    ∀ z ∈ (center (pCore 2 (parabolic L S j))).map (pCore 2 (parabolic L S j)).subtype,
      x*z=z*x := by
  let := h.finite_parabolic j
  let P := parabolic L S j
  let Z := coreCenter P
  let r := centerAction P
  let a := originalCubic h j f
  have hZ : Nat.card Z ≤ 4 := by
    rw [show Nat.card Z = Nat.card (center (pCore 2 P)) from
      card_map_of_injective (pCore 2 P).subtype_injective]
    exact original_second_core_center_card_le h j f
  have ha3 : r a ^ 3=1 := by rw [←map_pow,originalCubic_cube,map_one]
  have hx2 : r x ^ 2=1 := by rw [←map_pow,hx,map_one]
  have harx : r a * r x = r x * r a := by rw [←map_mul,←map_mul,hax]
  have hfix : ∀ z : Z,(r a) z=z → z=1 := by
    intro z hz
    have hc : a*(z : P)=(z : P)*a := by
      have hh := congrArg Subtype.val hz
      change a*(z : P)*a⁻¹=(z : P) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hzQ : (z : P) ∈ pCore 2 P := map_subtype_le _ z.property
    exact Subtype.ext (originalCubic_core_fixed h j f z hzQ hc)
  have hfixed := four_permutation_fixed hZ (r a).toEquiv (r x).toEquiv (1 : Z)
    (map_one (r a)) (map_one (r x))
    (fun z => by simpa [pow_succ,MulAut.mul_apply] using congrArg (fun t : MulAut Z => t z) ha3)
    (fun z => by simpa [pow_succ,MulAut.mul_apply] using congrArg (fun t : MulAut Z => t z) hx2)
    (fun z => by exact congrArg (fun t : MulAut Z => t z) harx) hfix
  intro z hz
  have hh := congrArg Subtype.val (hfixed (⟨z,hz⟩ : Z))
  change x*z*x⁻¹=z at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

/-- The exact outer relations can be chosen with both actors fixing every
central element of the unchanged core. Thus any marked z on this center is
fixed, without a separate z-fixing assumption. -/
theorem exists_original_outer_cubic_relations_fixing_core_center
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    ∃ k x : parabolic L S j,
      orderOf k = 3 ∧ (k : G) ∈ parabolic L (reducedSylow L S) j ∧
      x^2=1 ∧ (x : G) ∉ parabolic L (reducedSylow L S) j ∧
      originalCubic h j f * k = k * originalCubic h j f ∧
      originalCubic h j f * x = x * originalCubic h j f ∧
      x*k*x⁻¹=k⁻¹ ∧
      ∀ z ∈ (center (pCore 2 (parabolic L S j))).map (pCore 2 (parabolic L S j)).subtype,
        x*z=z*x ∧ k*z=z*k := by
  obtain ⟨k,x,hk,hkR,hx,hxR,hak,hax,hxk,_⟩ :=
    exists_original_outer_cubic_relations h i j e f hne
  have hxc := originalCubic_commuting_involution_fixes_core_center h j f x hx hax
  let P := parabolic L S j
  let Z := coreCenter P
  let r := centerAction P
  have hrx : r x=1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change x*(z : P)*x⁻¹=(z : P)
    rw [hxc z z.property,mul_inv_cancel_right]
  have hrk : r k = (r k)⁻¹ := by
    have hh := congrArg r hxk
    simpa only [map_mul,map_inv,hrx,one_mul,inv_one,mul_one] using hh
  have hrk2 : r k ^ 2=1 := by
    calc
      r k ^ 2 = r k * r k := pow_two _
      _ = (r k)⁻¹ * r k := congrArg (fun t => t * r k) hrk
      _ = 1 := inv_mul_cancel _
  have hk3 : k^3=1 := by simpa only [hk] using pow_orderOf_eq_one k
  have hrk3 : r k ^ 3=1 := by rw [←map_pow,hk3,map_one]
  have hrk1 : r k=1 := by
    rw [show (3 : ℕ)=2+1 from rfl,pow_succ,hrk2,one_mul] at hrk3
    exact hrk3
  refine ⟨k,x,hk,hkR,hx,hxR,hak,hax,hxk,?_⟩
  intro z hz
  refine ⟨hxc z hz,?_⟩
  have hh := congrArg (fun t : MulAut Z => (t (⟨z,hz⟩ : Z) : P)) hrk1
  change k*z*k⁻¹=z at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
