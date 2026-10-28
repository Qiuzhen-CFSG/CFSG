module

public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimeBound
public import Theory.GroupTheory.SolvableRadical.PrimaryResidualImage
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.PResidual.PrimeToCoreRestriction

/-!
# The original primary radical I_p=O^{p′}(O∞(L))

The actual quotient map L→L/O₂(L), followed by its actual local-component
image, carries I_p onto O_p(L/O₂(L)). Its kernel is O₂(I_p), giving the
source quotient identification. The radical is characteristic and
two-perfect. The canonical Ξ_p(L) belongs to I_p because its quotient is
a p-group and it is two-perfect; this does not assert any new starred
membership for I_p.

Source: Aschbacher--Smith 3.2.14, p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original primary solvable radical, included back in G. -/
@[expose] def primaryRadical (p : ℕ) (L : Subgroup G) : Subgroup G :=
  (primarySolvableResidual p L).map L.subtype

/-- The inclusion in L preserves characteristicity of the original primary radical. -/
instance primaryRadical_characteristic (p : ℕ) (L : Subgroup G) :
    ((primaryRadical p L).subgroupOf L).Characteristic := by
  change (((primarySolvableResidual p L).map L.subtype).comap L.subtype).Characteristic
  rw [comap_map_eq,ker_subtype,sup_bot_eq]
  infer_instance

/-- The original primary radical is two-perfect for every odd prime. -/
theorem primaryRadical_twoPerfect (L : Subgroup G) {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    IsPPerfect 2 (primaryRadical p L) := by
  have hp : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
  let f := L.subtype.comp (solvableRadical L).subtype
  have hr : (primeToResidual p (solvableRadical L)).map f = primaryRadical p L := by
    rw [← map_map]
    rfl
  let e := ((primeToResidual p (solvableRadical L)).equivMapOfInjective f
    (L.subtype_injective.comp (solvableRadical L).subtype_injective)).trans
      (MulEquiv.subgroupCongr hr)
  exact (isPPerfect_primeToResidual p 2 hp).of_surjective e.toMonoidHom e.surjective

/-- The actual primary radical modulo its own two-core is the full
prime core of the original local quotient. -/
def primaryRadicalQuotientEquiv
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    (primaryRadical p L ⧸ pCore 2 (primaryRadical p L)) ≃* pCore p (XiQuotient L) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun (A : Type u) _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun (A : Type u) _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hc := proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk hG hL.2.2) hL.1
  let e := radicalLocalQuotientEquiv hL
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsSolvable f.ker := inferInstance
  have hr : primarySolvableResidual p (radicalLocalImage T L) =
      pCore p (radicalLocalImage T L) := FittingActions.radical_primeToResidual_image hc.2 ho
  have hcore : pCore 2 (primarySolvableResidual p (radicalLocalImage T L)) = ⊥ := by
    rw [hr]
    have hdis := IsPGroup.disjoint_of_ne 2 p
      (by intro he; rw [← he] at ho; norm_num at ho)
      (pCore 2 (pCore p (radicalLocalImage T L))) ⊤ pCore_isPGroup
      (pCore_isPGroup.to_subgroup ⊤)
    exact bot_unique ((le_inf le_rfl le_top).trans hdis.le_bot)
  let ei := (primarySolvableResidual p L).equivMapOfInjective L.subtype L.subtype_injective
  let eqi := QuotientGroup.congr _ _ ei.symm (pCore_map_iso 2 ei.symm)
  let eqr := primarySolvableResidualQuotientEquiv p 2 f hf hk hcore
  let ep : pCore p (XiQuotient L) ≃* pCore p (radicalLocalImage T L) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))
  exact eqi.trans (eqr.trans ((MulEquiv.subgroupCongr hr).trans ep.symm))

private theorem coreEquiv_symm_apply_val {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (p : ℕ) (z : pCore p B) :
    e ((((e.subgroupMap (pCore p A)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso p e))).symm z : pCore p A) : A) = (z : B) := by
  exact congrArg (fun x : pCore p B => (x : B))
    (((e.subgroupMap (pCore p A)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso p e))).apply_symm_apply z)

/-- The primary quotient comparison retains the actual inclusion in L. -/
theorem primaryRadicalQuotientEquiv_apply_mk
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (x : primaryRadical p L) :
    (primaryRadicalQuotientEquiv hG T hL ho
      (QuotientGroup.mk' (pCore 2 (primaryRadical p L)) x) : XiQuotient L) =
      QuotientGroup.mk' (pCore 2 L) (inclusion (map_subtype_le _) x) := by
  let e := radicalLocalQuotientEquiv hL
  let ep : pCore p (XiQuotient L) ≃* pCore p (radicalLocalImage T L) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))
  have hep := coreEquiv_symm_apply_val e p

  apply e.injective
  dsimp only [primaryRadicalQuotientEquiv]
  change e (ep.symm _) = _
  rw [hep]
  have hk : IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsNilpotent (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).ker := hk.isNilpotent
  let : Group.IsSolvable (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))).ker := inferInstance
  let ei := (primarySolvableResidual p L).equivMapOfInjective L.subtype L.subtype_injective
  change (primarySolvableResidualQuotientEquiv p 2
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) _ _ _
    (QuotientGroup.mk' _ (ei.symm x)) : radicalLocalImage T L) = _
  refine (primarySolvableResidualQuotientEquiv_apply_mk p 2
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) _ _ _ (ei.symm x)).trans ?_
  change e (QuotientGroup.mk' (pCore 2 L) (ei.symm x).val) =
    e (QuotientGroup.mk' (pCore 2 L) (inclusion (map_subtype_le _) x))
  apply congrArg e
  apply congrArg (QuotientGroup.mk' (pCore 2 L))
  apply Subtype.ext
  exact congrArg (fun z : (primarySolvableResidual p L).map L.subtype => (z : G))
    (ei.apply_symm_apply x)


/-- The canonical radical lies in the literal solvable radical of L. -/
theorem XiP_le_solvableRadical (L : Subgroup G) (p : ℕ) [Fact p.Prime] :
    XiP p L ≤ (solvableRadical L).map L.subtype := by
  have hs : Group.IsSolvable (xiPPreimage p L) := by
    let q := QuotientGroup.mk' (pCore 2 L)
    let : Group.IsNilpotent q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isNilpotent
    let : Group.IsSolvable q.ker := inferInstance
    let : Group.IsNilpotent (xiOmegaCore p L) :=
      (((pCore_isPGroup (p := p) (G := XiQuotient L)).to_subgroup _).map _).isNilpotent
    let : Group.IsSolvable (xiOmegaCore p L) := inferInstance
    exact isSolvable_comap_of_solvable_ker q _
  have hpre : xiPPreimage p L ≤ solvableRadical L :=
    le_solvableRadical _ inferInstance hs
  exact map_mono (show xiPIn p L ≤ solvableRadical L from (map_subtype_le _).trans hpre)

/-- The original Ξ_p(L) lies in I_p, without asserting that I_p is a Xi member. -/
theorem XiP_le_primaryRadical (L : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hq : XiOddQuotient p (XiQuotient (XiP p L))) :
    XiP p L ≤ primaryRadical p L := by
  let R := (solvableRadical L).map L.subtype
  have hXR : XiP p L ≤ R := XiP_le_solvableRadical L p
  let Y := (XiP p L).subgroupOf R
  let e : Y ≃* XiP p L := subgroupOfEquivOfLe hXR
  let eq : (Y ⧸ pCore 2 Y) ≃* XiQuotient (XiP p L) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hy : primeToResidual p Y = ⊤ :=
    primeToResidual_eq_top_of_pGroup_quotient p 2 (pCore 2 Y) pCore_isPGroup
      (hq.isPGroup.of_equiv eq.symm)
      ((XiP_isPPerfect p L).of_surjective e.symm.toMonoidHom e.symm.surjective)
  have hle := map_mono (f := R.subtype) (le_primeToResidual_of_eq_top p Y hy)
  rw [map_subgroupOf_eq_of_le hXR] at hle
  have hr : (primeToResidual p R).map R.subtype = primaryRadical p L := by
    rw [← map_embedded_primeToResidual_of_hom p (solvableRadical L) L.subtype]
    rfl
  exact hle.trans_eq hr


omit [Finite G] in
/-- The actual primary radical is normalized by the full normalizer of L. -/
theorem normalizer_le_normalizer_primaryRadical (L : Subgroup G) (p : ℕ) :
    normalizer (L : Set G) ≤ normalizer (primaryRadical p L : Set G) :=
  normalizer_le_normalizer_characteristic_image L (primarySolvableResidual p L)

/-- Every actual primary radical quotient is an odd p-group. -/
theorem primaryRadical_quotient_isPGroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    IsPGroup p (primaryRadical p L ⧸ pCore 2 (primaryRadical p L)) :=
  pCore_isPGroup.of_equiv (primaryRadicalQuotientEquiv hG T hL ho).symm

/-- Non-exponent-p primary radicals are precisely the higher homocyclic
case used in the source contradiction, with p>5 proved by A.1.30. -/
theorem primaryRadical_higher_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hexp : ¬ ∀ x : primaryRadical p L ⧸ pCore 2 (primaryRadical p L), x ^ p = 1) :
    5 < p ∧ ∃ a : ℕ, 2 ≤ a ∧
      Nonempty ((primaryRadical p L ⧸ pCore 2 (primaryRadical p L)) ≃*
        Multiplicative (Fin 2 → ZMod (p^a))) := by
  let e := primaryRadicalQuotientEquiv hG T hL ho
  have he : ¬ ∀ x : pCore p (XiQuotient L), x ^ p = 1 := by
    intro h
    apply hexp
    intro x
    apply e.injective
    simpa only [map_pow,map_one] using h (e x)
  obtain ⟨hp,a,ha,⟨ea⟩⟩ := local_higher_core_structure hG T hL hn he
  exact ⟨hp,a,ha,⟨e.trans ea⟩⟩

end CFSG.Quasithin.Chapter3.RadicalCentralization
