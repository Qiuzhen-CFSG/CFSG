module
public import Stellmacher.SectionOne.OneSevenFactorPair
public import Stellmacher.SectionOne.OneSevenFactorConjugation
public import Stellmacher.SectionOne.OneASL2Factors
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products

/-!
# The normal global product in Stellmacher (1.7)

The finite family of all refined Ω-star factors generates a normal internal
direct product. Pairwise separation and centerlessness give the product,
while conjugation invariance gives normality. The local factorization of
each offender places J(V,S) inside this product. This realizes E₀ in the
proof of (1.7), journal p.19 of `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionOne
universe u

@[expose] public noncomputable def oneSevenFactors
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] : Finset (Subgroup G) := by
  classical
  let _ := Fintype.ofFinite {D : Subgroup G | IsOneSevenFactor (V := V) D}
  exact Set.toFinset {D : Subgroup G | IsOneSevenFactor (V := V) D}

@[expose] public noncomputable def oneSevenGenerated
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] : Subgroup G :=
  sSup {D : Subgroup G | IsOneSevenFactor (V := V) D}

@[simp] public theorem mem_oneSevenFactors_iff
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (D : Subgroup G) :
    D ∈ oneSevenFactors (G := G) (V := V) ↔ IsOneSevenFactor (V := V) D := by
  classical
  simp [oneSevenFactors]

private theorem generated_normal
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] :
    (oneSevenGenerated (G := G) (V := V)).Normal := by
  let E := oneSevenGenerated (G := G) (V := V)
  refine ⟨?_⟩
  intro x hx g
  have hle : E ≤ E.comap (MulAut.conj g).toMonoidHom := by
    apply sSup_le
    intro D hD d hd
    change g * d * g⁻¹ ∈ E
    have hDg : D.conjBy g ≤ E :=
      le_sSup (s := {D : Subgroup G | IsOneSevenFactor (V := V) D}) (hD.conjBy D g)
    exact hDg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hd)
  exact hle hx

public theorem oneSeven_global_product
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    (oneSevenGenerated (G := G) (V := V)).Normal ∧
    IsInternalDirectProduct (oneSevenGenerated (G := G) (V := V))
      (oneSevenFactors (G := G) (V := V)) ∧
    oneJ (G := G) (V := V) (S : Subgroup G) ≤
      oneSevenGenerated (G := G) (V := V) := by
  classical
  let F := oneSevenFactors (G := G) (V := V)
  let E := oneSevenGenerated (G := G) (V := V)
  let I := {D : Subgroup G // D ∈ F}
  let _ : Fintype I := Fintype.ofFinite I
  have hgen : E = ⨆ i : I, (i : Subgroup G) := by
    apply le_antisymm
    · apply sSup_le
      intro D hD
      exact le_iSup (fun i : I => (i : Subgroup G))
        ⟨D, (mem_oneSevenFactors_iff D).mpr hD⟩
    · apply iSup_le
      intro i
      exact le_sSup ((mem_oneSevenFactors_iff _).mp i.property)
  have himage : Finset.univ.image (fun i : I => (i : Subgroup G)) = F := by
    ext D
    simp [I]
  refine ⟨generated_normal, ?_, ?_⟩
  · change IsInternalDirectProduct E F
    rw [← himage]
    apply RankOneThreeGroupAssembly.internalDirectProduct_image_of_iSup_centerless_commuting
      E (fun i : I => (i : Subgroup G)) hgen
    · intro i
      exact RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two
        ((mem_oneSevenFactors_iff _).mp i.property).1
    · intro i j hij
      exact (oneSevenFactor_eq_or_commute h i j
        ((mem_oneSevenFactors_iff _).mp i.property)
        ((mem_oneSevenFactors_iff _).mp j.property)).resolve_left
        (fun heq => hij (Subtype.ext heq))
  · apply sSup_le
    intro A hA
    by_cases hAne : A = ⊥
    · rw [hAne]
      exact bot_le
    obtain ⟨FA, hprod, hFA⟩ := oneA_sl2_factors h S A hA hAne
    apply le_trans (show A ≤ ⁅oddCore G, A⁆ ⊔ A from le_sup_right)
    rw [hprod.1]
    apply iSup_le
    intro D
    exact le_sSup (hFA D D.property)

end Stellmacher.SectionOne
