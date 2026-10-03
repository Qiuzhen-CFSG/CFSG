module

public import Stellmacher.SectionOne.OneSevenGlobalProduct
public import Stellmacher.SectionOne.OneSevenOddCoreProduct
public import Stellmacher.UniqueMaximalContainingMap
public import Theory.GroupTheory.UniqueMaximalComplementFactors

/-!
# The odd core is the canonical derived product

Suppose the odd core supplements a Sylow two-subgroup which has a unique
maximal overgroup. Under the faithful Section One action hypotheses, the
existence of an actual canonical factor forces the odd core to equal the
derived subgroup of the full canonical product.

The (1.7)(a) decomposition writes the odd core as that derived subgroup
times its centralizer of the full product. Both subgroups are normal in
the ambient group, because the full canonical product is normal. Their
join is disjoint from the Sylow subgroup by coprime orders. The bounded
unique-maximal complement theorem makes one factor trivial; the selected
canonical factor contributes a derived subgroup of order three, so the
centralizer factor must be trivial.

This is the odd-factor generation step used in Stellmacher (9.10)(3),
printed p.57 of `refs/files/stellmacher-n-group.pdf`. Its local supplement
and unique-maximal hypotheses are supplied separately in the geometric
application, rather than inferred merely from existence of a transvection.
-/

namespace Stellmacher.SectionOne

universe u

public theorem oneSeven_oddCore_eq_derived_of_unique_maximal
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) (sylow : Sylow 2 G)
    (hgen : oddCore G ⊔ (sylow : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup G) ⊤)
    (factor : Subgroup G) (hfactor : IsOneSevenFactor (V := V) factor) :
    oddCore G =
      (commutator (oneSevenGenerated (G := G) (V := V))).map
        (oneSevenGenerated (G := G) (V := V)).subtype := by
  let E := oneSevenGenerated (G := G) (V := V)
  let R := (commutator E).map E.subtype
  let C := oddCore G ⊓ Subgroup.centralizer (E : Set G)
  obtain ⟨hEnormal, hproduct, _⟩ := oneSeven_global_product hyp sylow
  let _ : E.Normal := hEnormal
  let _ : R.Normal := by
    dsimp only [R]
    rw [Subgroup.map_subtype_commutator]
    infer_instance
  let _ : (oddCore G).Normal := pPrimeCore_normal
  let _ : C.Normal := inferInstance
  have hsplit := oneSevenFactor_oddCore_product E (oneSevenFactors (G := G) (V := V))
    hproduct (fun D hD => (mem_oneSevenFactors_iff D).mp hD)
  have hjoin : oddCore G = R ⊔ C := by
    rw [hsplit.1]
    apply le_antisymm
    · apply iSup_le
      intro i
      by_cases hi : i = 0
      · simpa only [hi, ↓reduceIte] using (show R ≤ R ⊔ C from le_sup_left)
      · simpa only [hi, ↓reduceIte] using (show C ≤ R ⊔ C from le_sup_right)
    · apply sup_le
      · exact (by simpa only [↓reduceIte] using
          (le_iSup (fun i : Fin 2 => if i = 0 then R else C) 0))
      · exact (by simpa using (le_iSup (fun i : Fin 2 => if i = 0 then R else C) 1))
  have hRC : Disjoint R C := by
    simpa only [↓reduceIte, one_ne_zero] using hsplit.2.1 0 1 (by decide)
  have hWS : Disjoint (oddCore G) (sylow : Subgroup G) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := sylow.isPGroup'.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).symm.pow_right n
  have hRnot : R ≠ ⊥ := by
    intro hbot
    have hfactorE : factor ≤ E := le_sSup hfactor
    have hderived : (commutator factor).map factor.subtype ≤ R := by
      dsimp only [R]
      rw [Subgroup.map_subtype_commutator, Subgroup.map_subtype_commutator]
      exact Subgroup.commutator_mono hfactorE hfactorE
    have hfactorBot := bot_unique (hderived.trans hbot.le)
    have hcard := hfactor.2.1.2.1
    rw [hfactorBot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨maximal, hmaximal, hsylow, huniq⟩ :=
    (uniqueMaximalContaining_top_iff (sylow : Subgroup G)).mp hunique
  have hCbot : C = ⊥ :=
    (Subgroup.eq_bot_or_eq_bot_of_normal_complement_unique_maximal R C sylow
      hRC (hjoin ▸ hWS) (hjoin ▸ hgen)
      ⟨maximal, ⟨hmaximal, hsylow⟩, fun K hK => huniq K hK.1 hK.2⟩).resolve_left hRnot
  rw [hjoin, hCbot, sup_bot_eq]

end Stellmacher.SectionOne
