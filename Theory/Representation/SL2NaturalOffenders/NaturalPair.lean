module
public import Theory.Representation.BinaryOffender.ProductSplitting
public import Theory.Representation.SL2NaturalOffenders.Ratios
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Offenders on two literal natural SL₂ factors

The independent coordinate actions have no strong offenders. The product
splitting theorem therefore makes every offender the full product of its
projections; each nontrivial projection is a defining Sylow subgroup.
The final maps retain an arbitrary faithful actor embedding and the actual
equivariant quotient, as needed for the two-factor B.6.9 decomposition.
Source: Aschbacher–Smith B.6.10 and E.2.3(2), pp.117 and216–217.
-/

open Subgroup Representation.BinaryOffender
namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => NoStrong.Actor F
local notation "N" => NoStrong.natural (F := F)

public noncomputable abbrev naturalPair : Representation (ZMod 2) (D × D) ((Fin 2 → F) × (Fin 2 → F)) :=
  Representation.prod (MonoidHom.comp N (MonoidHom.fst D D))
    (MonoidHom.comp N (MonoidHom.snd D D))

public theorem naturalPair_not_strong : ¬ IsStrongFFModule (naturalPair (F := F)) :=
  product_not_strong N N NoStrong.natural_not_strong NoStrong.natural_not_strong

private theorem offender_or_bot_sylow {A : Subgroup D}
    (hA : A = ⊥ ∨ IsOffender N A) : ∃ P : Sylow 2 D, A = ⊥ ∨ A = (P : Subgroup D) := by
  rcases hA with hA | hA
  · exact ⟨Classical.arbitrary (Sylow 2 D),Or.inl hA⟩
  · obtain ⟨P,hP⟩ := exists_sylow_of_le ⊤ topEquiv N (fun _ _ => rfl) hA le_top
    refine ⟨P.mapSurjective (f := (topEquiv (G := D)).toMonoidHom) (topEquiv (G := D)).surjective,Or.inr ?_⟩
    exact hP.symm

public theorem naturalPair_offender {A : Subgroup (D × D)}
    (hA : IsOffender (naturalPair (F := F)) A) :
    ∃ P Q : Sylow 2 D,
      A = (A.map (MonoidHom.fst D D)).prod (A.map (MonoidHom.snd D D)) ∧
      (A.map (MonoidHom.fst D D) = ⊥ ∨ A.map (MonoidHom.fst D D) = (P : Subgroup D)) ∧
      (A.map (MonoidHom.snd D D) = ⊥ ∨ A.map (MonoidHom.snd D D) = (Q : Subgroup D)) := by
  obtain ⟨hs,h₁,h₂⟩ := offender_product_of_not_strong N N
    NoStrong.natural_not_strong NoStrong.natural_not_strong hA
  obtain ⟨P,hP⟩ := offender_or_bot_sylow h₁
  obtain ⟨Q,hQ⟩ := offender_or_bot_sylow h₂
  exact ⟨P,Q,hs,hP,hQ⟩

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
public theorem naturalPair_quotient_offender
    (ρ : Representation (ZMod 2) G V) (j : G →* D × D) (hj : Function.Injective j)
    (f : V →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F))) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = naturalPair (F := F) (j g) (f v))
    {A : Subgroup G} (hA : IsOffender ρ A) :
    ∃ P Q : Sylow 2 D,
      A.map j = ((A.map j).map (MonoidHom.fst D D)).prod
        ((A.map j).map (MonoidHom.snd D D)) ∧
      ((A.map j).map (MonoidHom.fst D D) = ⊥ ∨
        (A.map j).map (MonoidHom.fst D D) = (P : Subgroup D)) ∧
      ((A.map j).map (MonoidHom.snd D D) = ⊥ ∨
        (A.map j).map (MonoidHom.snd D D) = (Q : Subgroup D)) := by
  have hc := fixedCodim_le_of_equivariant_surjection ρ ((naturalPair (F := F)).comp j) f hf he A
  apply naturalPair_offender (F := F)
  exact IsOffender.map_equivariant ((naturalPair (F := F)).comp j) (naturalPair (F := F)) j hj
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl) ⟨hA.1,hc.trans hA.2⟩

omit [Finite G] in
public theorem not_strong_of_naturalPair_quotient
    (ρ : Representation (ZMod 2) G V) (j : G →* D × D) (hj : Function.Injective j)
    (f : V →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F))) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = naturalPair (F := F) (j g) (f v)) : ¬ IsStrongFFModule ρ := by
  rintro ⟨A,hA⟩
  have hc := fixedCodim_le_of_equivariant_surjection ρ ((naturalPair (F := F)).comp j) f hf he A
  have hAm := (IsOffender.map_equivariant ((naturalPair (F := F)).comp j) (naturalPair (F := F)) j hj
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl) ⟨hA.1,(hc.trans_lt hA.2).le⟩).1
  apply naturalPair_not_strong (F := F) ⟨A.map j,hAm,?_⟩
  rw [rank_map_injective j hj]
  change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (naturalPair (F := F)) (A.map j)) < _
  rw [←fixedSpace_comp_map (naturalPair (F := F)) j A]
  exact hc.trans_lt hA.2
/-- The actual best-offender layer is enough; ambient actors may permute the two factors. -/
public theorem not_strong_of_naturalPair_layer
    (ρ : Representation (ZMod 2) G V) (Y : Subgroup G)
    (hY : offenderSubgroup ρ ≤ Y)
    (j : Y →* D × D) (hj : Function.Injective j)
    (f : V →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F))) (hf : Function.Surjective f)
    (he : ∀ (g : Y) v, f (ρ (g : G) v) = naturalPair (F := F) (j g) (f v)) :
    ¬ IsStrongFFModule ρ := by
  rintro ⟨A,hA⟩
  obtain ⟨B,_,hB,hBs⟩ := hA.exists_bestOffender ρ
  have hBY : B ≤ Y := (hB.le_offenderSubgroup ρ).trans hY
  apply not_strong_of_naturalPair_quotient (ρ.comp Y.subtype) j hj f hf he
  refine ⟨B.subgroupOf Y,((show IsOffender ρ B from ⟨hBs.1,hBs.2.le⟩).subgroupOf ρ hBY).1,?_⟩
  rw [fixedCodim_subgroupOf ρ hBY,rank_subgroupOf hBY]
  exact hBs.2
end Representation.SL2NaturalOffenders
