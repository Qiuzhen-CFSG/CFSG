module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.Torsion

/-!
# Movement and a fixed diagonal for the same paired Hall conjugator

Cauchy supplies a nonidentity p-element in the abelian factor. Disjointness
from its t-conjugate proves that t moves it. If t² centralizes the factor's
p-torsion, the product with its t-conjugate is a nonidentity fixed point.
Both witnesses belong to the literal ambient Ω₁(Oₚ(A)) and use the same t.
Their combination is incompatible with the common quotient power action.

The square-centralizer condition is essential to this local argument:
factor exchange alone does not imply it. The source application must
construct the Hall factors and a conjugator satisfying that condition
from the actual rank-one component and natural Cartan geometry.
These remaining constructions are owned by the parameter-component task;
this module is not an unconditional proof of component normality.

Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial abelian factor exchanged disjointly by t supplies both a
moved p-point and a nonidentity fixed diagonal, for that same t. The square
condition is retained on the actual p-torsion, not inferred from exchange. -/
theorem exchanged_primeTorsion_mixed (A B : Subgroup G) [IsMulCommutative A]
    (hBA : B ≤ A) (p : ℕ) [Fact p.Prime] (hpB : p ∣ Nat.card B)
    (t : G) (ht : t ∈ normalizer (A : Set G))
    (hd : Disjoint B (B.map (MulAut.conj t).toMonoidHom))
    (hsq : t ^ 2 ∈ centralizer (primeTorsion B p : Set G)) :
    (∃ x ∈ primeTorsion A p, t*x*t⁻¹ ≠ x) ∧
      ∃ z ∈ primeTorsion A p, z ≠ 1 ∧ t*z*t⁻¹ = z := by
  let : IsMulCommutative B := .of_setLike_mul_comm fun a ha b hb =>
    setLike_mul_comm (hBA ha) (hBA hb)
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp (primeTorsion_ne_bot B p hpB)
  have haG : (a : G) ≠ 1 := fun he => ha (Subtype.ext he)
  have haB : (a : G) ∈ B := primeTorsion_le B p a.property
  have haA : (a : G) ∈ A := hBA haB
  have hap : (a : G) ^ p = 1 := (mem_primeTorsion_iff B p a).mp a.property |>.2
  have haP : (a : G) ∈ primeTorsion A p := (mem_primeTorsion_iff A p a).mpr ⟨haA,hap⟩
  let b : G := t * a * t⁻¹
  have hbA : b ∈ A := (ht a).mp haA
  have hbP : b ∈ primeTorsion A p := (primeTorsion_normalizer A p ht a).mp haP
  have hbC : b ∈ B.map (MulAut.conj t).toMonoidHom := mem_map_of_mem _ haB
  have hm : b ≠ a := by
    intro he
    exact haG (disjoint_def.mp hd haB (he ▸ hbC))
  have hc : (a : G) * b = b * a := setLike_mul_comm haA hbA
  have hbback : t*b*t⁻¹ = a := by
    have he := (mem_centralizer_iff.mp hsq) a a.property
    calc
      t*b*t⁻¹ = t^2 * a * (t^2)⁻¹ := by dsimp [b]; simp only [pow_two]; group
      _ = a := by rw [← he]; group
  have hzP : (a : G)*b ∈ primeTorsion A p := (primeTorsion A p).mul_mem haP hbP
  have hz1 : (a : G)*b ≠ 1 := by
    intro he
    have hae : (a : G) = b⁻¹ := eq_inv_of_mul_eq_one_left he
    exact haG (disjoint_def.mp hd haB (hae ▸ (B.map _).inv_mem hbC))
  refine ⟨⟨a,haP,hm⟩,⟨a*b,hzP,hz1,?_⟩⟩
  calc
    t*((a : G)*b)*t⁻¹ = (t*a*t⁻¹)*(t*b*t⁻¹) := by group
    _ = b*a := by rw [hbback]
    _ = a*b := hc.symm

/-- Subgroup form of the two witnesses, retaining the same conjugator.
This is the exact mixed-action input to the common-power contradiction. -/
theorem exchanged_primeTorsion_centralizer (A B : Subgroup G) [IsMulCommutative A]
    (hBA : B ≤ A) (p : ℕ) [Fact p.Prime] (hpB : p ∣ Nat.card B)
    (t : G) (ht : t ∈ normalizer (A : Set G))
    (hd : Disjoint B (B.map (MulAut.conj t).toMonoidHom))
    (hsq : t ^ 2 ∈ centralizer (primeTorsion B p : Set G)) :
    (¬ primeTorsion A p ≤ centralizer ({t} : Set G)) ∧
      primeTorsion A p ⊓ centralizer ({t} : Set G) ≠ ⊥ := by
  obtain ⟨⟨x,hx,hm⟩,⟨z,hz,hz1,hfix⟩⟩ :=
    exchanged_primeTorsion_mixed A B hBA p hpB t ht hd hsq
  constructor
  · intro h
    apply hm
    have he := mem_centralizer_singleton_iff.mp (h hx)
    rw [← he,mul_inv_cancel_right]
  · intro he
    have hzC : z ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul).mp hfix).symm
    exact hz1 (mem_bot.mp (he ▸ (show z ∈ primeTorsion A p ⊓ centralizer {t} from ⟨hz,hzC⟩)))

/-- Application to the literal L/O₂(L) quotient: an exchanged Hall factor
with a nontrivial p-part cannot have one common quotient power action. -/
theorem no_exchanged_primeTorsion_of_quotient_power
    (A B L : Subgroup G) [IsMulCommutative A] (hBA : B ≤ A)
    (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpB : p ∣ Nat.card B)
    (hL : primeTorsion A p ≤ L) (t : G) (ht : t ∈ normalizer (A : Set G))
    (hd : Disjoint B (B.map (MulAut.conj t).toMonoidHom))
    (hsq : t ^ 2 ∈ centralizer (primeTorsion B p : Set G))
    (ha : ∀ (x : G) (hx : x ∈ primeTorsion A p),
      QuotientGroup.mk' (pCore 2 L)
        ⟨t*x*t⁻¹,hL ((primeTorsion_normalizer A p ht x).mp hx)⟩ =
          (QuotientGroup.mk' (pCore 2 L) ⟨x,hL hx⟩) ^ k) : False := by
  obtain ⟨hm,hf⟩ := exchanged_primeTorsion_centralizer A B hBA p hpB t ht hd hsq
  exact no_mixed_action_of_quotient_power A L p k hp2 hL t ht ha hm hf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
