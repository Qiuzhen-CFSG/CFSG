module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedReduction
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.PResidual.Quotient

/-!
# The actual local residual in the equality-model exclusions

Let X = O²(C_M(z)). Its centralization of the natural layer implies
[L,X] ≤ O₂(L); the residual product lemma therefore makes X L-invariant.
Natural irreducibility makes V ∩ X either trivial or all of V. In a
symmetric actor model, the sign character detects the marked normal
generator and excludes the latter possibility.

For a non-two pair carried into C_M(z), the core-residual and center
clauses of 6.2.6 place z in X. This gives the literal residual contradiction
needed by 6.2.13. Construction of those pairs from the symmetric models,
and the canonical extraspecial-pair assembly, remain with
qt-d-1222-equality-action-pair; its parent source assembly is
qt-d-1222-recognition-equality-geometry.

Source: Aschbacher--Smith, 6.2.13, printed p.687 (PDF p.704).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The residual X = O²(C_M(z)), embedded in the original ambient group. -/
def equalityLocalResidual (M : Subgroup G) (z : G) : Subgroup G :=
  (pResidual 2 (centralizer ({z} : Set G) ⊓ M : Subgroup G)).map
    (centralizer ({z} : Set G) ⊓ M).subtype

/-- The source residual is normalized by L. Its commutators with L lie in
O₂(L), since it centralizes the faithful natural layer. -/
theorem LocalAnalysis.equalityLocalResidual_normalized
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    L ≤ normalizer (equalityLocalResidual M z : Set G) := by
  let D := centralizer ({z} : Set G) ⊓ M
  let Q := L.pCoreIn 2
  have hLV : L ≤ normalizer (layer L R : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural.2.1
    exact hmodel.normalizes
  have hLC : L ≤ normalizer (centralizer (layer L R : Set G) : Set G) :=
    hLV.trans ((normal_subgroupOf_iff_le_normalizer
      (centralizer_le_normalizer (layer L R : Set G))).mp inferInstance)
  have hQM : Q ≤ M := (pCoreIn_le 2 L).trans h611.L_le
  have hQC : Q ≤ centralizer (layer L R : Set G) :=
    (natural_centralizer_eq_core hnatural.2.1).symm.le.trans inf_le_right
  have hQD : Q ≤ D := le_inf
    (hQC.trans (centralizer_le (Set.singleton_subset_iff.mpr (show z ∈ layer L R from hz.1)))) hQM
  have hXL : equalityLocalResidual M z ≤ normalizer (L : Set G) :=
    (map_subtype_le _).trans (inf_le_right.trans
      ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal))
  apply normalizes_residual_of_commutator_le_two L D D Q D.le_normalizer hQD
    (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  change ⁅L, equalityLocalResidual M z⁆ ≤ Q
  rw [show Q = L ⊓ centralizer (layer L R : Set G) from
    (natural_centralizer_eq_core hnatural.2.1).symm]
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hXL)
    ((commutator_mono le_rfl A.residual_centralizes).trans
      (le_normalizer_iff_commutator_le_right.mp hLC))

/-- Irreducibility reduces the residual intersection to the two genuine
possibilities. The sign of the surviving action model rules out containment. -/
theorem LocalAnalysis.equalityLocalResidual_intersection
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    layer L R ⊓ equalityLocalResidual M z = ⊥ ∨
      layer L R ≤ equalityLocalResidual M z := by
  have hLV : L ≤ normalizer (layer L R : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural.2.1
    exact hmodel.normalizes
  rcases hnatural.2.1.invariant_subgroup
      (layer L R ⊓ equalityLocalResidual M z) inf_le_left
      ((le_inf hLV (A.equalityLocalResidual_normalized h611 hnatural hz)).trans
        inf_normalizer_le_normalizer_inf) with h | h
  · exact Or.inl h
  · exact Or.inr (h.symm.le.trans inf_le_right)

/-- A two-group quotient detecting a layer element forces the exact source
intersection V ∩ O²(C_M(z)) to be trivial. In 6.2.13 the quotient is the
sign of the classified action. Its construction remains with this task. -/
theorem LocalAnalysis.equalityLocalResidual_disjoint_of_detected
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    {B : Type*} [Group B]
    (χ : (centralizer ({z} : Set G) ⊓ M : Subgroup G) →* B)
    (hB : IsPGroup 2 B)
    (hdetect : ∃ v : (centralizer ({z} : Set G) ⊓ M : Subgroup G),
      (v : G) ∈ layer L R ∧ χ v ≠ 1) :
    layer L R ⊓ equalityLocalResidual M z = ⊥ := by
  rcases A.equalityLocalResidual_intersection h611 hnatural hz with h | h
  · exact h
  · obtain ⟨v, hv, hχ⟩ := hdetect
    obtain ⟨x, hx, he⟩ := h hv
    have hxv : x = v := Subtype.ext he
    exact (hχ (pResidual_le_ker_of_isPGroup 2 χ hB (hxv ▸ hx))).elim

omit [Finite G] in
/-- A non-two pair carried into C_M(z) places z in the actual residual
O²(C_M(z)). This is the source use of 6.2.6 in the symmetric-model exclusion. -/
theorem LocalAnalysis.equalityLocalResidual_contains_involution_of_pair
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (g : G) (hg : g ∈ centralizer ({z} : Set G))
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G))
    (x : G) (hx : x ∈ centralizer ({z} : Set G))
    (hpair : (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom ≤ centralizer ({z} : Set G) ⊓ M) :
    z ∈ equalityLocalResidual M z := by
  let J := layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom
  let D := centralizer ({z} : Set G) ⊓ M
  have hgz : g * z * g⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hxz : x * z * x⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  have hzI : z ∈ layer L R ⊓ (layer L R).map (MulAut.conj g).toMonoidHom :=
    ⟨hz.1, ⟨z, hz.1, hgz⟩⟩
  obtain ⟨_, _, hres, hcenter⟩ := A.non_two_pair g hleft hright hnon
  rw [hcenter] at hzI
  obtain ⟨c, hc, hcz⟩ := hzI
  have hcR : c ∈ pResidual 2 J := hres (map_subtype_le _ hc)
  let f : J →* D := ((MulAut.conj x).toMonoidHom.comp J.subtype).codRestrict D
    (fun j => hpair (mem_map_of_mem (MulAut.conj x).toMonoidHom j.property))
  have hm := mem_map_of_mem D.subtype
    (map_pResidual_le 2 f (mem_map_of_mem f hcR))
  change x * (c : G) * x⁻¹ ∈ equalityLocalResidual M z at hm
  change (c : G) = z at hcz
  rwa [hcz, hxz] at hm

/-- The detected residual and a source non-two pair give the contradiction
needed for the symmetric alternatives. All pair and quotient premises remain
literal; their construction belongs to the equality-action owner. -/
theorem LocalAnalysis.equality_excludes_pair_in_local_normalizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    {B : Type*} [Group B]
    (χ : (centralizer ({z} : Set G) ⊓ M : Subgroup G) →* B)
    (hB : IsPGroup 2 B)
    (hdetect : ∃ v : (centralizer ({z} : Set G) ⊓ M : Subgroup G),
      (v : G) ∈ layer L R ∧ χ v ≠ 1)
    (g : G) (hg : g ∈ centralizer ({z} : Set G))
    (hleft : (layer L R ⊓ normalizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex (layer L R) = 2)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G))
    (x : G) (hx : x ∈ centralizer ({z} : Set G))
    (hpair : (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom ≤ centralizer ({z} : Set G) ⊓ M) : False := by
  have hm : z ∈ layer L R ⊓ equalityLocalResidual M z :=
    ⟨hz.1, A.equalityLocalResidual_contains_involution_of_pair hz g hg hleft hright hnon x hx hpair⟩
  rw [A.equalityLocalResidual_disjoint_of_detected h611 hnatural hz χ hB hdetect, mem_bot] at hm
  have ho := horder
  rw [hm, orderOf_one] at ho
  norm_num at ho

/-- Every symmetric actor model makes the source residual disjoint from V.
The marked involution normally generates the actor, so its sign is nontrivial;
the sign pulled back to C_M(z) supplies the detecting two-group quotient. -/
theorem LocalAnalysis.equalityLocalResidual_disjoint_of_symmetric_actor
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      ZS (T : Subgroup G) L R)
    (m : ℕ) (e : EqualityActor z ≃* Equiv.Perm (Fin (m + 2))) :
    layer L R ⊓ equalityLocalResidual M z = ⊥ := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  obtain ⟨a, ha, _, _, _, hgen, _⟩ :=
    A.equality_action_classification h611 hnatural hz horder hTH hbranch
  let χ₀ : EqualityActor z →* ℤˣ := Equiv.Perm.sign.comp e.toMonoidHom
  have hsurj : Function.Surjective χ₀ :=
    (Equiv.Perm.sign_surjective (Fin (m + 2))).comp e.surjective
  have haχ : χ₀ a ≠ 1 := by
    intro he
    have hker : normalClosure ({a} : Set (EqualityActor z)) ≤ χ₀.ker :=
      normalClosure_le_normal (Set.singleton_subset_iff.mpr he)
    rw [hgen] at hker
    obtain ⟨b, hb⟩ := hsurj (-1)
    have hb1 : χ₀ b = 1 := hker (mem_top b)
    rw [hb] at hb1
    exact (by decide : (-1 : ℤˣ) ≠ 1) hb1
  let D := centralizer ({z} : Set G) ⊓ M
  let χ : D →* ℤˣ := χ₀.comp
    ((QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))).comp (inclusion inf_le_left))
  have htwo : IsPGroup 2 ℤˣ := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro u
    refine ⟨1, ?_⟩
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  apply A.equalityLocalResidual_disjoint_of_detected h611 hnatural hz χ htwo
  obtain ⟨v, hv, hvq⟩ := ha
  let d : D := ⟨v.val, v.property, h611.sylow_le (h611.layer_le_T hv)⟩
  refine ⟨d, hv, ?_⟩
  change χ₀ (QuotientGroup.mk' _ v) ≠ 1
  rwa [hvq]

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
