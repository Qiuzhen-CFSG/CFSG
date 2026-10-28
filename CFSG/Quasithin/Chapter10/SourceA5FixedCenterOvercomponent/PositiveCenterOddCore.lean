module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalFixedPair
public import CFSG.Quasithin.Chapter10.SourceA5EscapingOrthogonalAction
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy.Characteristic
public import Theory.GroupTheory.OddCoreKleinFourCentralizers
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.IndexTwoConjugateSpan

/-!
# The odd core of the original second-vector centralizer

The two original fixed vectors have a diagonal in the center of T. This
involution does not centralize L, while the positive-center hypothesis
supplies an independent central involution centralizing the whole block
orbit. Their four-group has characteristic-two involution centralizers,
so the Klein-four odd-core theorem applies to the actual second vector.

Source: Aschbacher–Smith 10.2.1, printed p.743; the odd-core step is the
standard central-four consequence of even characteristic.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem layer_fixed_disjoint (K : Subgroup G) (hK : IsAlternatingBlock K 5) :
    Disjoint ((blockU K).map K.subtype) (centralizer (K : Set G)) := by
  rw [Subgroup.disjoint_def]
  rintro z ⟨u,hu,rfl⟩ hc
  have huc : u ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext (hc k k.property)
  have hz : blockU K ⊓ center K = ⊥ := by
    rw [←blockFixed_map,hK.blockFixed_eq_bot,Subgroup.map_bot]
  exact congrArg Subtype.val (show u=1 from hz.le ⟨hu,huc⟩)

private theorem original_pair_diagonal_central
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (p : SourceA5OriginalFixedPair D t) :
    p.first * p.second ∈ omegaOneCenterAmbient (T : Subgroup G) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hi : (R.subgroupOf (T : Subgroup G)).index = 2 := by
    change R.relIndex (T : Subgroup G) = 2
    dsimp only [R]
    rw [inf_relIndex_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  have hfix₁ (r : G) (hr : r ∈ R) : r * p.first = p.first * r :=
    mem_centralizer_singleton_iff.mp (p.first_centralizer.symm.le hr).2
  have hfix₂ (r : G) (hr : r ∈ R) : r * p.second = p.second * r :=
    mem_centralizer_singleton_iff.mp (p.second_centralizer.symm.le hr).2
  have hs : t^2 ∈ R := (R.subgroupOf (T : Subgroup G)).sq_mem_of_index_two hi ⟨t,ht⟩
  have he : (MulAut.conj t) p.second = p.first := by
    rw [p.conjugate]
    change t * (t * p.first * t⁻¹) * t⁻¹ = p.first
    have h := hfix₁ (t^2) hs
    rw [pow_two] at h
    calc
      t * (t * p.first * t⁻¹) * t⁻¹ = (t*t*p.first)*t⁻¹*t⁻¹ := by group
      _ = (p.first*(t*t))*t⁻¹*t⁻¹ := by rw [h]
      _ = p.first := by group
  let := D.module_elementary
  have hc : p.first * p.second = p.second * p.first := by
    exact congrArg Subtype.val (mul_comm (⟨p.first,p.first_module⟩ : D.moduleSubgroup)
      ⟨p.second,p.second_module⟩)
  have htd : t ∈ centralizer ({p.first*p.second} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    change (MulAut.conj t) (p.first*p.second) = p.first*p.second
    rw [map_mul, ←p.conjugate, he, hc]
  have hRd : R ≤ centralizer ({p.first*p.second} : Set G) := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    calc
      r*(p.first*p.second) = (r*p.first)*p.second := by rw [mul_assoc]
      _ = (p.first*r)*p.second := by rw [hfix₁ r hr]
      _ = p.first*(p.second*r) := by rw [mul_assoc,hfix₂ r hr]
      _ = (p.first*p.second)*r := by rw [mul_assoc]
  refine (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨mul_mem p.first_sylow p.second_sylow,
    elemPow_eq_one_of_isElementaryAbelian (p := 2) _
      (D.moduleSubgroup.mul_mem p.first_module p.second_module), ?_⟩
  intro x hx
  apply mem_centralizer_singleton_iff.mp
  by_cases hxR : x ∈ R
  · exact hRd hxR
  · have hxt : x*t⁻¹ ∈ R := by
      apply ((R.subgroupOf (T : Subgroup G)).mul_mem_iff_of_index_two hi
        (a := ⟨x,hx⟩) (b := ⟨t⁻¹,inv_mem ht⟩)).mpr
      change x ∈ R ↔ t⁻¹ ∈ R
      rw [inv_mem_iff]
      exact iff_of_false hxR (fun hh => htn hh.2)
    simpa using (centralizer ({p.first*p.second} : Set G)).mul_mem (hRd hxt) htd



/-- The actual second-vector centralizer has trivial odd core. -/
theorem source_a5_original_second_centralizer_oddCore_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (p : SourceA5OriginalFixedPair D t) :
    pPrimeCore 2 (centralizer ({p.second} : Set G)) = ⊥ := by
  let E := omegaOneCenterAmbient (T : Subgroup G)
  let d := p.first*p.second
  have hd : d ∈ E := original_pair_diagonal_central D hn ht htn p
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hdout : d ∉ centralizer (L : Set G) := by
    intro hdC
    have hf : p.first ∈ centralizer (L : Set G) := by
      simpa [d] using (centralizer (L : Set G)).mul_mem hdC
        ((centralizer (L : Set G)).inv_mem p.second_opposite)
    exact p.first_ne (Subgroup.disjoint_def.mp (layer_fixed_disjoint L hL) p.first_layer hf)
  obtain ⟨z,hz,hzne⟩ :=
    (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)).bot_or_exists_ne_one.resolve_left
      (source_a5_fixed_center_ne_bot_of_escape D e hn hout)
  have hzL : z ∈ centralizer (L : Set G) := centralizer_le (le_componentOrbit L T) hz.2
  have hzpow := (mem_omegaOneCenterAmbient_iff _ _).mp hz.1
  have hdpow := (mem_omegaOneCenterAmbient_iff _ _).mp hd
  let Z := zpowers z ⊔ zpowers d
  have hZE : Z ≤ E := sup_le (zpowers_le.mpr hz.1) (zpowers_le.mpr hd)
  let := omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le hZE
  have hZcard : Nat.card Z = 4 := by
    have hdN : d ∈ normalizer (zpowers z : Set G) := by
      apply Subgroup.centralizer_le_normalizer _
      rw [zpowers_eq_closure,centralizer_closure]
      exact mem_centralizer_singleton_iff.mpr (hzpow.2.2 d hdpow.1)
    have hdnot : d ∉ zpowers z := fun hm => hdout ((zpowers_le.mpr hzL) hm)
    dsimp only [Z]
    rw [card_sup_zpowers_of_normalizing_involution _ _ hdpow.2.1 hdnot hdN,
      Nat.card_zpowers,orderOf_eq_prime hzpow.2.1 hzne]
  have ha : orderOf p.second = 2 := by
    let := D.module_elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ p.second_module)
      p.second_ne
  apply pPrimeCore_centralizer_eq_bot_of_klein_four p.second ha Z hZcard
  · intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp (hZE hv)).2.2 p.second p.second_sylow).symm
  · intro v hv hvne
    have hvE := (mem_omegaOneCenterAmbient_iff _ _).mp (hZE hv)
    have hvord : orderOf v = 2 := orderOf_eq_prime hvE.2.1 hvne
    have hp : IsPGroup 2 (zpowers v) := by
      let := IsElementaryAbelian.zpowers_of_pow_eq_one hvE.2.1
      exact IsElementaryAbelian.isPGroup 2 _
    have hne : zpowers v ≠ ⊥ := by
      intro he
      exact hvne (mem_bot.mp (he ▸ mem_zpowers v))
    apply Chapter1.mem_He_iff.mp
    apply Chapter1.twoLocal_mem_He_of_sylow_le T (D.simpleQTKE.evenCharacteristic T)
    · exact ⟨zpowers v,hne,hp,
        (normalizer_zpowers_eq_centralizer_of_order_two v hvord).symm⟩
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hvE.2.2 x hx)

end CFSG.Quasithin.Chapter10
