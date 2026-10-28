module

public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition
public import Mathlib.GroupTheory.Complement

/-!
# Two full roots identify their prescribed complement

Two distinct defining-characteristic Sylow images generate the full rank-one
group. If the original roots lie in a specified complement to the entire
kernel, injectivity there identifies their literal join with that same
complement. The resulting isomorphism is the restriction of the original map.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

/-- The literal join of two full roots is the prescribed kernel complement,
with its rank-one marking given by the original quotient homomorphism. -/
theorem opposite_roots_eq_complement
    {E F : Type*} [Group E] [Field F] [Finite F] [CharP F 2]
    (q : E →* SL(2,F)) (K : Subgroup E) (hK : q.ker.IsComplement' K)
    (R S : Subgroup E) (hRK : R ≤ K) (hSK : S ≤ K)
    (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hr : Nat.card R = Nat.card F) (hs : Nat.card S = Nat.card F)
    (hne : R.map q ≠ S.map q) :
    R ⊔ S = K ∧ ∃ e : (R ⊔ S : Subgroup E) ≃* SL(2,F),
      ∀ x, e x = q (x : E) := by
  have hiK : Function.Injective (q.comp K.subtype) := by
    apply (q.comp K.subtype).ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hK.disjoint.le_bot ⟨hx,x.property⟩)
  have hi (U : Subgroup E) (hu : U ≤ K) : Function.Injective (q.subgroupMap U) := by
    intro x y hxy
    apply Subtype.ext
    have he : (⟨x,hu x.property⟩ : K) = ⟨y,hu y.property⟩ :=
      hiK (congrArg Subtype.val hxy)
    exact congrArg (fun z : K => (z : E)) he
  have hcard (U : Subgroup E) (hu : U ≤ K) : Nat.card (U.map q) = Nat.card U :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap U)
      ⟨hi U hu,q.subgroupMap_surjective U⟩).toEquiv).symm
  obtain ⟨P,hP⟩ := (hR.map q).exists_le_sylow
  obtain ⟨Q,hQ⟩ := (hS.map q).exists_le_sylow
  have hSylow (X : Sylow 2 SL(2,F)) : Nat.card X = Nat.card F := by
    rw [← Nat.card_congr (sylowEquivAdditive F 2 X).toEquiv]
    rfl
  have hrP : R.map q = (P : Subgroup SL(2,F)) :=
    eq_of_le_of_card_ge hP (by rw [hcard R hRK,hr,hSylow P])
  have hsQ : S.map q = (Q : Subgroup SL(2,F)) :=
    eq_of_le_of_card_ge hQ (by rw [hcard S hSK,hs,hSylow Q])
  have hgen : (R ⊔ S).map q = ⊤ := by
    rw [Subgroup.map_sup,hrP,hsQ]
    apply sylow_sup_eq_top 2 P Q
    intro he
    exact hne (hrP.trans ((congrArg Sylow.toSubgroup he).trans hsQ.symm))
  have hjoin : R ⊔ S = K := by
    apply le_antisymm (sup_le hRK hSK)
    intro k hk
    obtain ⟨x,hx,hxq⟩ := (hgen.symm ▸ mem_top (q k) : q k ∈ (R ⊔ S).map q)
    have he : (⟨x,(sup_le hRK hSK) hx⟩ : K) = ⟨k,hk⟩ := hiK hxq
    have hxk : x = k := congrArg (fun z : K => (z : E)) he
    rwa [←hxk]
  let f := q.comp (R ⊔ S).subtype
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : K => (z : E)) (hiK (a₁ := ⟨x,(sup_le hRK hSK) x.property⟩)
      (a₂ := ⟨y,(sup_le hRK hSK) y.property⟩) he)
  have hfs : Function.Surjective f := by
    intro g
    obtain ⟨x,hx,hxg⟩ := (hgen.symm ▸ mem_top g : g ∈ (R ⊔ S).map q)
    exact ⟨⟨x,hx⟩,hxg⟩
  exact ⟨hjoin,MulEquiv.ofBijective f ⟨hfi,hfs⟩,fun _ => rfl⟩

end Matrix.SpecialLinearGroup
