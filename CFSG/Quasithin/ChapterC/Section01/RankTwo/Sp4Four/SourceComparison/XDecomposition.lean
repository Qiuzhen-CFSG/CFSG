module
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedSaturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry

/-!
# The literal X decomposition from the critical root movement budget

Four conjugates of the critical symplectic root generate the component.
Their fixed-codimension budget is attained by the natural moving cover,
so that cover and the component-fixed subspace span the whole X-layer.
The original multiplicative embedding converts this equality to
X = U C_X(L), preserving the entire central attachment.

Source: MS93 (3.3)(ii)(2), printed p.867. The original coordinate and
movement producers are applied in `OriginalXDecomposition`.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour Representation.SymplecticFourOrthogonalCover
variable {H : Type*} [Group H] {R : Subgroup H} {a : Vertex R}
  {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The four-root budget gives the literal original X decomposition. The
moving cover, X embedding, and full component conjugation retain their given
quotient conventions; the original critical movement bound remains explicit. -/
theorem X_eq_moving_sup_centralizer_of_root_budget (hF : 2 < Nat.card F)
    (σ : Representation (ZMod 2) (L (K := F)) V) (W : Subrepresentation σ)
    (p : W.toRepresentation.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (A : Subgroup (L (K := F))) (hc : Nat.card A = Nat.card F)
    (hd : Module.finrank F (displacementSpace (A.map (commutator (Sp F)).subtype)) = 1)
    (hq : ∀ x ∈ A.map (commutator (Sp F)).subtype,
      ∀ y ∈ A.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hbound : fixedCodim σ A ≤ Module.finrank (ZMod 2) F)
    (j : Multiplicative V →* FreeAmalgam R) (hj : j.range = X R a)
    (hW : (j.comp W.toSubmodule.subtype.toAddMonoidHom.toMultiplicative).range = U R a)
    (f : Ltilde R a →* L (K := F))
    (hconj : ∀ (g : Ltilde R a) (v : V),
      j (Multiplicative.ofAdd (σ (f g) v)) =
        (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹) :
    X R a = U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  have hs := sup_fixed_eq_top_of_root_budget hF σ W p hp A hc hd hq hbound
  have hUX : U R a ≤ X R a := by
    intro x hx
    rw [←hW] at hx
    obtain ⟨v,rfl⟩ := hx
    rw [←hj]
    exact ⟨Multiplicative.ofAdd v.toAdd.val,rfl⟩
  apply le_antisymm
  · intro x hx
    rw [←hj] at hx
    obtain ⟨v,rfl⟩ := hx
    have hv : v.toAdd ∈ W.toSubmodule ⊔ fixedSpace σ ⊤ := by rw [hs]; trivial
    obtain ⟨u,hu,c,hc,huc⟩ := Submodule.mem_sup.mp hv
    have hju : j (Multiplicative.ofAdd u) ∈ U R a := by
      rw [←hW]
      exact ⟨Multiplicative.ofAdd ⟨u,hu⟩,rfl⟩
    have hjc : j (Multiplicative.ofAdd c) ∈
        X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
      refine ⟨hj ▸ ⟨Multiplicative.ofAdd c,rfl⟩,?_⟩
      change j (Multiplicative.ofAdd c) ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))
      intro g hg
      have he := hconj ⟨g,hg⟩ c
      have hf := hc (⟨f ⟨g,hg⟩,mem_top _⟩ : (⊤ : Subgroup (L (K := F))))
      change σ (f ⟨g,hg⟩) c = c at hf
      rw [hf] at he
      have hm := congrArg (fun z : FreeAmalgam R => z*g) he
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm.symm
    have he : j v = j (Multiplicative.ofAdd u) * j (Multiplicative.ofAdd c) := by
      rw [←map_mul]
      congr 1
      exact congrArg Multiplicative.ofAdd huc.symm
    rw [he]
    exact (U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)))).mul_mem
      ((show U R a ≤ U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set _)) from le_sup_left) hju)
      ((show X R a ⊓ centralizer (Ltilde R a : Set _) ≤
        U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set _)) from le_sup_right) hjc)
  · exact sup_le hUX inf_le_left

/-- The literal movement bound supplies the fixed-codimension budget. -/
theorem X_eq_moving_sup_centralizer_of_movement (hF : 2 < Nat.card F)
    (σ : Representation (ZMod 2) (L (K := F)) V) (W : Subrepresentation σ)
    (p : W.toRepresentation.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (Z : Subgroup (FreeAmalgam R)) (β : Z →* L (K := F))
    (hc : Nat.card β.range = Nat.card F)
    (hd : Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype)) = 1)
    (hq : ∀ x ∈ β.range.map (commutator (Sp F)).subtype,
      ∀ y ∈ β.range.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (j : Multiplicative V →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = X R a)
    (hW : (j.comp W.toSubmodule.subtype.toAddMonoidHom.toMultiplicative).range = U R a)
    (hβ : ∀ (z : Z) (v : V), j (Multiplicative.ofAdd (σ (β z) v)) =
      (z : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (z : FreeAmalgam R)⁻¹)
    (hbound : (centralizer (Z : Set (FreeAmalgam R))).relIndex (X R a) ≤ Nat.card F)
    (f : Ltilde R a →* L (K := F))
    (hconj : ∀ (g : Ltilde R a) (v : V), j (Multiplicative.ofAdd (σ (f g) v)) =
      (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹) :
    X R a = U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  apply X_eq_moving_sup_centralizer_of_root_budget hF σ W p hp β.range hc hd hq ?_
    j hjr hW f hconj
  have hi := embedded_centralizer_index σ (X R a) Z j hj hjr β hβ
  rw [hi] at hbound
  have hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [hcard] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
