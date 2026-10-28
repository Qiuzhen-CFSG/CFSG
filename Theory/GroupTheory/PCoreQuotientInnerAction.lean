module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.NormNum

/-!
# Inner actions from a marked two-core quotient

A normal subgroup with trivial two-core embeds into the ambient two-core
quotient. If its marked image fills one direct factor, every ambient
conjugation on it is inner. The other factor is retained in the hypothesis,
so the criterion applies to the literal two-block parabolic quotient.
A centerless two-core quotient also excludes a central subgroup of order
three, since its image would be central and its kernel a two-group.

Source application: Aschbacher--Smith 12.5.3, printed pp.817--818.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

-- An inner-action criterion which retains the two quotient factors.
theorem exists_inner_action_of_twoCore_product {X U W : Type*} [Group X] [Finite X]
    [Group U] [Group W] [Finite W] (B : Subgroup X) [B.Normal]
    (hb : pCore 2 B = ⊥) (hc : Nat.card B = Nat.card W)
    (e : (X ⧸ pCore 2 X) ≃* U × W)
    (hsmall : ∀ b : B, (e (QuotientGroup.mk' _ (b : X))).1 = 1) :
    ∀ x : X, ∃ b : B, ∀ y : B, x * (y : X) * x⁻¹ = (b : X) * y * (b : X)⁻¹ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let g := (MonoidHom.snd U W).comp (f.comp B.subtype)
  have hker : (pCore 2 X).subgroupOf B ≤ pCore 2 B :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  have hfi : Function.Injective (f.comp B.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro b he
    have hq : QuotientGroup.mk' (pCore 2 X) (b : X) = 1 :=
      e.injective (he.trans e.map_one.symm)
    have hmem : (b : X) ∈ pCore 2 X := (QuotientGroup.eq_one_iff (b : X)).mp hq
    have hb' := hker hmem
    simpa only [hb,mem_bot] using hb'
  have hgi : Function.Injective g := by
    intro b c he
    apply hfi
    exact Prod.ext ((hsmall b).trans (hsmall c).symm) he
  have hgs := ((Nat.bijective_iff_injective_and_card g).mpr ⟨hgi,hc⟩).2
  intro x
  obtain ⟨b,hb'⟩ := hgs (f x).2
  refine ⟨b,fun y => ?_⟩
  have hi : ∀ (z : X) (y : B), z * (y : X) * z⁻¹ ∈ B :=
    fun z y => (inferInstance : B.Normal).conj_mem y y.property z
  have he : f (x * (y : X) * x⁻¹) = f ((b : X) * y * (b : X)⁻¹) := by
    simp only [map_mul,map_inv]
    apply Prod.ext
    · change (f x).1 * (f y).1 * ((f x).1)⁻¹ =
        (f b).1 * (f y).1 * ((f b).1)⁻¹
      simp only [show (f y).1 = 1 from hsmall y,mul_one,mul_inv_cancel]
    · change (f x).2 * (f y).2 * ((f x).2)⁻¹ =
        (f b).2 * (f y).2 * ((f b).2)⁻¹
      change (f b).2 = (f x).2 at hb'
      rw [hb']
  exact congrArg Subtype.val (hfi (a₁ := ⟨_,hi x y⟩) (a₂ := ⟨_,hi b y⟩) he)


-- A centerless two-core quotient cannot contain a central odd-order element.
theorem no_central_three_of_centerless_twoCore_quotient {X C : Type*} [Group X] [Finite X] [Group C] [Finite C]
    (e : C →* X) (he : Function.Injective e) (hc : Nat.card C = 3)
    (hz : e.range ≤ center X) (hquot : center (X ⧸ pCore 2 X) = ⊥) : False := by
  have hr : e.range ≤ pCore 2 X := by
    intro x hx
    have hxc := hz hx
    have hq : QuotientGroup.mk' (pCore 2 X) x ∈ center (X ⧸ pCore 2 X) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) y
      simpa only [←map_mul] using congrArg (QuotientGroup.mk' (pCore 2 X))
        (mem_center_iff.mp hxc y)
    rw [hquot,mem_bot] at hq
    exact (QuotientGroup.eq_one_iff x).mp hq
  have hd := card_dvd_of_le hr
  rw [←Nat.card_congr (MonoidHom.ofInjective he).toEquiv,hc] at hd
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  rw [hn] at hd
  have hbad := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at hbad


end Theory.GroupTheory
