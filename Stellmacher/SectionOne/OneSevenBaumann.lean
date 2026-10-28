module

public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionOne.OneSevenModuleProduct
public import Stellmacher.SectionOne.OneSevenFixedSpaceNormalizer
public import Theory.Representation.CardFourTwoGroupImage

/-!
# The Baumann subgroup in Stellmacher (1.7)

The Baumann subgroup B is exactly J(V,S). The global identification already
realizes J as the Sylow intersection of the normal product of one-seven
factors. Since B fixes CV(J), the fixed-space normalizer theorem shows that
B preserves each factor and its four-element support. It also fixes the
complement CV(E0). The module decomposition and ambient faithfulness therefore
embed B in the product of its actions on these supports. Each image is a
two-group in GL2(2), hence has order at most two. Their product bounds |B| by
two to the number of factors, which is precisely |J| by the Sylow-coordinate
count. Finally J≤B follows directly from the definitions, so equality holds.

This proves the last paragraph of Stellmacher (1.7), journal page 19,
refs/latex/stellmacher-n-group.tex. The argument also covers trivial J and
does not use an additional inner-normalizer decomposition.
-/

namespace Stellmacher.SectionOne
universe u

/-- A faithful action preserving four-point supports and fixing their common
complement has two-group actor order at most two to the number of supports. -/
public theorem moduleProduct_card_bound
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (B E : Subgroup G) {n : ℕ} (D : Fin n → Subgroup G)
    (hnorm : ∀ i, B ≤ Subgroup.normalizer (D i : Set G))
    (hmodule : IsInternalDirectProductFamily (⊤ : Subgroup V)
      (fun i : Option (Fin n) => match i with
        | none => FixedPoints.subgroup E V
        | some i => commutatorAction (D i) V))
    (hfix : B ≤ fixingSubgroup G (FixedPoints.subgroup E V : Set V))
    (hB : IsPGroup 2 B) (hU : ∀ i, Nat.card (commutatorAction (D i) V) = 4) :
    Nat.card B ≤ 2 ^ n := by
  classical
  let U (i : Fin n) : Subgroup V := commutatorAction (D i) V
  let _ (i : Fin n) : IsInvariant B V (U i) :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor B (D i) (hnorm i)
  let ρ (i : Fin n) : B →* MulAut (U i) := MulDistribMulAction.toMulAut B (U i)
  let f : B →* (∀ i, (ρ i).range) := MonoidHom.pi fun i => (ρ i).rangeRestrict
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro b hb
      have hbfix (i : Fin n) (v : V) (hv : v ∈ U i) : (b : G) • v = v := by
        have hρ : ρ i b = 1 := congrArg Subtype.val (congrFun (MonoidHom.mem_ker.mp hb) i)
        have hact := MulEquiv.congr_fun hρ (⟨v, hv⟩ : U i)
        exact congrArg Subtype.val hact
      have hbV : ∀ v : V, (b : G) • v = v := by
        intro v
        have hv : v ∈ (⊤ : Subgroup V) := Subgroup.mem_top v
        rw [hmodule.1, Subgroup.iSup_eq_closure] at hv
        refine Subgroup.closure_induction (p := fun v _ => (b : G) • v = v)
          ?_ ?_ ?_ ?_ hv
        · intro x hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          cases i with
          | none => exact (mem_fixingSubgroup_iff (M := G)).mp (hfix b.property) x hi
          | some i => exact hbfix i x hi
        · exact smul_one b.val
        · intro x y _ _ hx hy
          rw [smul_mul', hx, hy]
        · intro x _ hx
          rw [smul_inv', hx]
      have hbG : (b : G) ∈ fixingSubgroup G (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        exact fun v _ => hbV v
      rw [h.action_faithful] at hbG
      exact Subtype.ext hbG
    · exact bot_le
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_pi] at hcard
  have hle : ∏ i : Fin n, Nat.card (ρ i).range ≤ ∏ _i : Fin n, 2 := by
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i hi
    let _ : IsElementaryAbelian 2 (U i) :=
      RankOneThreeGroupAssembly.isElementaryAbelian_subgroup (U i)
    exact Representation.card_action_image_le_two_of_card_four hB (hU i)
  exact hcard.trans (by simpa using hle)

private theorem oneSeven_baumann_data
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    let B := oneB (V := V) (S : Subgroup G)
    let J := oneJ (V := V) (S : Subgroup G)
    let E₀ := oneSevenGenerated (G := G) (V := V)
    ∃ (n : ℕ) (D : Fin n → Subgroup G),
      (∀ i, Nat.card (commutatorAction (D i) V) = 4) ∧
      (∀ i, B ≤ Subgroup.normalizer (D i : Set G)) ∧
      IsInternalDirectProductFamily (⊤ : Subgroup V)
        (fun i : Option (Fin n) => match i with
          | none => FixedPoints.subgroup E₀ V
          | some i => commutatorAction (D i) V) ∧
      B ≤ fixingSubgroup G (FixedPoints.subgroup E₀ V : Set V) ∧
      Nat.card J = 2 ^ n ∧ J ≤ B := by
  classical
  let B := oneB (V := V) (S : Subgroup G)
  let J := oneJ (V := V) (S : Subgroup G)
  let E₀ := oneSevenGenerated (G := G) (V := V)
  let F := oneSevenFactors (G := G) (V := V)
  obtain ⟨hEnormal,hprod,hJE⟩ := oneSeven_global_product h S
  obtain ⟨hJid,_hEid⟩ := oneSeven_global_identification h S
  change J = (S : Subgroup G) ⊓ E₀ at hJid
  change IsInternalDirectProduct E₀ F at hprod
  have hF : ∀ D ∈ F, IsOneSevenFactor (V := V) D :=
    fun D hD => (mem_oneSevenFactors_iff D).mp hD
  have hJleS : J ≤ (S : Subgroup G) := by rw [hJid]; exact inf_le_left
  have hJp : IsPGroup 2 J := S.isPGroup'.of_injective
    (Subgroup.inclusion hJleS) (Subgroup.inclusion_injective hJleS)
  have hJcard : Nat.card J = 2 ^ F.card := by
    rw [hJid]
    exact (sl2_product_sylow_coordinates S E₀ hEnormal F hprod
      (fun D hD => (hF D hD).1)).2.2.1
  have hJB : J ≤ B := by
    refine le_inf hJleS ?_
    intro j hj
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact (FixedPoints.mem_subgroup (M := J) (a := v)).mp hv ⟨j,hj⟩
  have hBfix : B ≤ fixingSubgroup G (FixedPoints.subgroup E₀ V : Set V) := by
    intro b hb
    rw [mem_fixingSubgroup_iff]
    intro v hv
    apply (mem_fixingSubgroup_iff (M := G)).mp hb.2 v
    change v ∈ FixedPoints.subgroup J V
    rw [FixedPoints.mem_subgroup]
    intro j
    exact (FixedPoints.mem_subgroup (M := E₀) (a := v)).mp hv ⟨j,hJE j.property⟩
  let I := {D : Subgroup G // D ∈ F}
  let n := Fintype.card I
  let eI : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup G := fun i => (eI i).val
  have hDi (i : Fin n) : D i ∈ F := (eI i).property
  have hinj : Function.Injective D := by
    intro i j hij
    exact eI.injective (Subtype.ext hij)
  have hgen : E₀ = ⨆ i : Fin n, D i := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro K
      obtain ⟨i,rfl⟩ := eI.surjective K
      exact le_iSup D i
    · apply iSup_le
      intro i
      exact le_iSup (fun K : I => (K : Subgroup G)) (eI i)
  refine ⟨n,D,?_,?_,?_,hBfix,?_,hJB⟩
  · exact fun i => (hF (D i) (hDi i)).2.2.1
  · intro i
    have hDE : D i ≤ E₀ := by rw [hgen]; exact le_iSup D i
    have hnorm : J ≤ Subgroup.normalizer (D i : Set G) := hJE.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hDE).mp (hprod.2.1 (D i) (hDi i)))
    exact (show B ≤ fixingSubgroup G (FixedPoints.subgroup J V : Set V) from inf_le_right).trans
      (oneSevenFactor_fixedSpace_normalizes h (D i) J (hF (D i) (hDi i)) hJp hnorm)
  · exact oneSevenFactor_module_product h D (fun i => hF (D i) (hDi i)) hinj E₀ hgen
  · simpa [n,I] using hJcard


public theorem oneSeven_baumann_eq_j
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    oneB (V := V) (S : Subgroup G) = oneJ (V := V) (S : Subgroup G) := by
  obtain ⟨n, D, hU, hnorm, hmodule, hfix, hJcard, hJB⟩ := oneSeven_baumann_data h S
  let B := oneB (V := V) (S : Subgroup G)
  have hB : IsPGroup 2 B := S.isPGroup'.of_injective
    (Subgroup.inclusion (show B ≤ (S : Subgroup G) from inf_le_left))
    (Subgroup.inclusion_injective inf_le_left)
  have hc := moduleProduct_card_bound h B (oneSevenGenerated (V := V)) D hnorm
    hmodule hfix hB hU
  exact (Subgroup.eq_of_le_of_card_ge hJB (by rwa [hJcard])).symm

end Stellmacher.SectionOne

