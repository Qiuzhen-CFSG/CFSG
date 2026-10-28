module
public import Stellmacher.SectionOne.LemmaOneSeven
public import Stellmacher.SectionOne.OneSevenFactorOrbitTransitivity


/-!
# The small fixed-index consequence of the one-seven decomposition

For the faithful elementary abelian action of Section One, suppose the
one-seven product generates the group with its Sylow two-subgroup, that
Sylow has a unique maximal overgroup, and the product has trivial fixed
space. If the module has more than four elements and the fixed space of
`J(V,S)` has at most four times the order of the Sylow-fixed space, then
the module has sixteen elements and the canonical one-seven family has
exactly two factors.

Choose a factor generating with the Sylow. Its order-two Sylow coordinate
fixes twice as many points as the whole factor. The Sylow-fixed space
intersects the factor-fixed space trivially, so the relative-index formula
bounds the Sylow-fixed space by two elements. The support modules of
canonical factors form a genuine independent product: every other factor
fixes a chosen support, and coprime splitting separates that support from
its fixed complement. Hence `|V|=4^n`, while the Sylow-coordinate theorem
gives `|J|=2^n`. The offender inequality and the given fixed-index bound
force `n≤3`. Sylow transitivity makes `n` a power of two, and `|V|>4`
excludes `n≤1`, leaving exactly two factors.

This is the numerical application of Stellmacher (1.7) in (9.3), Journal
of Algebra 190 (1997), p.50. All subgroups and fixed spaces use the supplied
action; the theorem does not identify the ambient group with a wreath
product without a separate group-realization argument.
-/

namespace Stellmacher.SectionOne
universe u
open scoped IsMulCommutative
open RankOneThreeGroupAssembly

private theorem fixed_card_le_two_of_generating_factor
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (D : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D)
    (hgen : D ⊔ (S : Subgroup G) = ⊤)
    (hQcard : Nat.card ((S : Subgroup G) ⊓ D : Subgroup G) = 2)
    (hfix : FixedPoints.subgroup (⊤ : Subgroup G) V = ⊥) :
    Nat.card (FixedPoints.subgroup S V) ≤ 2 := by
  let C := FixedPoints.subgroup D V
  let X := FixedPoints.subgroup S V
  let Y := FixedPoints.subgroup (↥((S : Subgroup G) ⊓ D)) V
  have hXY : X ≤ Y := by
    intro v hv y
    exact hv ⟨y, y.property.1⟩
  have hCX : C ⊓ X = ⊥ := by
    apply SetLike.coe_injective
    change (MulAction.fixedPoints D V ∩ MulAction.fixedPoints S V) = (⊥ : Subgroup V)
    rw [← fixedPoints_subgroup_sup, hgen]
    exact congrArg SetLike.coe hfix
  have hindex : C.relIndex Y = 2 :=
    oneSevenFactor_involution_fixed_relIndex h.action_faithful D
      ((S : Subgroup G) ⊓ D) hD inf_le_right hQcard
  have hcard : Nat.card X = C.relIndex X := by
    rw [← Subgroup.inf_relIndex_right, hCX, Subgroup.relIndex_bot_left]
  rw [hcard, ← hindex]
  exact Subgroup.relIndex_le_of_le_right hXY (by rw [hindex]; decide)

private theorem support_disjoint_fixed
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D : Subgroup G) (hD : IsOneSevenFactor (V := V) D) :
    Disjoint (commutatorAction D V) (FixedPoints.subgroup D V) := by
  let F := (commutator D).map D.subtype
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [show Nat.card F = 3 from hD.2.1.2.1, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := F)
    (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := V)).comm x y)
    hcop (inferInstance : IsMulCommutative V)
  rw [← oneSevenFactor_full_commutator_eq_derived D hD] at hcompl
  have hfixed : FixedPoints.subgroup D V ≤ FixedPoints.subgroup F V := by
    intro v hv
    rw [FixedPoints.mem_subgroup] at hv ⊢
    intro f
    exact hv ⟨f, Subgroup.map_subtype_le _ f.property⟩
  exact hcompl.disjoint.symm.mono_right hfixed

private theorem support_join_card
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (F : Finset (Subgroup G))
    (hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D) :
    Nat.card (F.sup (fun D => commutatorAction D V) : Subgroup V) = 4 ^ F.card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert D F hDF ih =>
    have hD := hF D (by simp)
    have hrest : ∀ E ∈ F, IsOneSevenFactor (V := V) E :=
      fun E hE => hF E (Finset.mem_insert_of_mem hE)
    have hfix : F.sup (fun E => commutatorAction E V) ≤ FixedPoints.subgroup D V := by
      apply Finset.sup_le
      intro E hE
      exact oneSevenFactor_commutatorAction_le_fixedPoints h D E hD (hrest E hE)
        (fun he => hDF (he ▸ hE))
    have hdis : Disjoint (commutatorAction D V) (F.sup (fun E => commutatorAction E V)) :=
      (support_disjoint_fixed D hD).mono_right hfix
    rw [Finset.sup_insert, natCard_sup_eq_mul_of_disjoint_of_le_centralizer _ _ hdis
      (by intro a ha b hb; exact (IsMulCommutative.is_comm (M := V)).comm b a),
      hD.2.2.1, ih hrest, Finset.card_insert_of_notMem hDF, pow_succ, Nat.mul_comm]

private theorem canonical_support_card
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hfix : FixedPoints.subgroup (oneE (V := V) (S : Subgroup G)) V = ⊥) :
    Nat.card V = 4 ^ (oneSevenFactors (G := G) (V := V)).card := by
  classical
  let F := oneSevenFactors (G := G) (V := V)
  let E := oneSevenGenerated (G := G) (V := V)
  let I := {D : Subgroup G // D ∈ F}
  let n := Fintype.card I
  let eI : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup G := fun i => (eI i).val
  have hD (i : Fin n) : IsOneSevenFactor (V := V) (D i) :=
    (mem_oneSevenFactors_iff _).mp (eI i).property
  have hinj : Function.Injective D := fun i j hij => eI.injective (Subtype.ext hij)
  have hgen : E = ⨆ i, D i := by
    apply le_antisymm
    · apply sSup_le
      intro K hK
      obtain ⟨i, hi⟩ := eI.surjective ⟨K, (mem_oneSevenFactors_iff K).mpr hK⟩
      have he : D i = K := congrArg Subtype.val hi
      rw [← he]
      exact le_iSup D i
    · apply iSup_le
      intro i
      exact le_sSup (hD i)
  have hm := (oneSevenFactor_module_product h D hD hinj E hgen).1
  have hfixE : FixedPoints.subgroup E V = ⊥ := by
    have heq := congrArg (fun A : Subgroup G => FixedPoints.subgroup A V)
      (oneSeven_global_identification h S).2
    exact heq.symm.trans hfix
  rw [iSup_option, hfixE, bot_sup_eq] at hm
  change (⊤ : Subgroup V) = ⨆ i, commutatorAction (D i) V at hm
  have hjoin : F.sup (fun K => commutatorAction K V) = ⊤ := by
    rw [hm]
    apply le_antisymm
    · apply Finset.sup_le
      intro K hK
      obtain ⟨i, hi⟩ := eI.surjective ⟨K, hK⟩
      have he : D i = K := congrArg Subtype.val hi
      rw [← he]
      exact le_iSup (fun i : Fin n => commutatorAction (D i) V) i
    · apply iSup_le
      intro i
      exact Finset.le_sup (f := fun K : Subgroup G => commutatorAction K V) (eI i).property
  have hc := support_join_card h F (fun K hK => (mem_oneSevenFactors_iff K).mp hK)
  rw [hjoin, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv] at hc
  exact hc

/-- A fixed-space index bound of four forces two canonical factors and a
sixteen-element faithful module under the local generation hypotheses. -/
public theorem oneSeven_card_sixteen_of_small_fixed_index
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hJ : oneJ (V := V) (S : Subgroup G) ≠ ⊥)
    (hgen : oneE (V := V) (S : Subgroup G) ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    (hfix : FixedPoints.subgroup (oneE (V := V) (S : Subgroup G)) V = ⊥)
    (hlarge : 4 < Nat.card V)
    (hindex : Nat.card (FixedPoints.subgroup (oneJ (V := V) (S : Subgroup G)) V) ≤
      4 * Nat.card (FixedPoints.subgroup S V)) :
    Nat.card V = 16 ∧ (oneSevenFactors (G := G) (V := V)).card = 2 := by
  classical
  let F := oneSevenFactors (G := G) (V := V)
  let E := oneSevenGenerated (G := G) (V := V)
  let J := oneJ (V := V) (S : Subgroup G)
  obtain ⟨hnormal, hproduct, _⟩ := oneSeven_global_product h S
  have hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D :=
    fun D hD => (mem_oneSevenFactors_iff D).mp hD
  have hcoord := sl2_product_sylow_coordinates S E hnormal F hproduct
    (fun D hD => (hF D hD).1)
  obtain ⟨D, hD, hDS⟩ := oneSeven_exists_factor_sup_sylow_eq_top h S hgen hunique
  have hfixTop : FixedPoints.subgroup (⊤ : Subgroup G) V = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfix]
    intro v hv e
    exact hv ⟨e, trivial⟩
  have hfixS := fixed_card_le_two_of_generating_factor h S D (hF D hD) hDS
    (hcoord.2.2.2 D hD) hfixTop
  have hfixJ : Nat.card (FixedPoints.subgroup J V) ≤ 8 := by
    change Nat.card (FixedPoints.subgroup J V) ≤ 4 * Nat.card (FixedPoints.subgroup S V) at hindex
    omega
  have hJcard : Nat.card J = 2 ^ F.card := by
    have heq := congrArg (fun A : Subgroup G => Nat.card A) (oneSeven_global_identification h S).1
    exact heq.trans hcoord.2.2.1
  have hVcard : Nat.card V = 4 ^ F.card := canonical_support_card h S hfix
  have hm := (lemma_one_seven h S hJ).part_b.2.2.2
  have hprodBound : Nat.card V ≤ Nat.card (FixedPoints.subgroup J V) * Nat.card J := by
    have hpos : (0 : ℚ) < Nat.card (FixedPoints.subgroup J V) * Nat.card J := by
      exact_mod_cast Nat.mul_pos (Nat.card_pos) (Nat.card_pos)
    change (Nat.card V : ℚ) / (Nat.card (FixedPoints.subgroup J V) * Nat.card J) ≤ 1 at hm
    have hh := (div_le_iff₀ hpos).mp hm
    simp only [one_mul] at hh
    exact_mod_cast hh
  have hnum : 2 ^ F.card ≤ 8 := by
    have hbase : 4 ^ F.card = 2 ^ F.card * 2 ^ F.card := by rw [← mul_pow]; norm_num
    rw [hVcard, hJcard, hbase] at hprodBound
    have hpos : 0 < 2 ^ F.card := pow_pos (by decide) _
    nlinarith
  have hsmall : F.card ≤ 3 := by
    by_contra hnot
    have hh : 2 ^ 4 ≤ 2 ^ F.card := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hh
    omega
  have hbig : 1 < F.card := by
    by_contra hnot
    have hh : 4 ^ F.card ≤ 4 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hVcard] at hh
    norm_num at hh
    omega
  obtain ⟨k, hk⟩ := oneSevenFactors_card_eq_two_pow h S hgen hunique
  change F.card = 2 ^ k at hk
  have hk1 : k = 1 := by
    have hklt : k < 2 := by
      by_contra hnot
      have hh : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at hh
      omega
    interval_cases k
    · norm_num at hk
      omega
    · rfl
  have htwo : F.card = 2 := by simpa [hk1] using hk
  exact ⟨by rw [hVcard, htwo]; norm_num, htwo⟩

end Stellmacher.SectionOne
