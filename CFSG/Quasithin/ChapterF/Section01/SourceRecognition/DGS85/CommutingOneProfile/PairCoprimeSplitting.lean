module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairFixedSpaces
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiOddFixedSpaces
public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.Representation.QuadraticFourGroup.TensorClassification.NaturalAction

/-!
# Odd actors splitting the Chapter 11 beta core

For a linear beta quotient, or Sz(2^(2m+1)) with m > 0, the two full
omega-centers generate the whole quotient. Descend the literal two-seed
section to this actor. Its complementary fixed spaces satisfy DGS (5.11),
so a nonidentity odd-order matrix fixes only the zero section vector.
Lift that matrix to an odd-order element y of the original center pair.
Coprime decomposition and [Q_beta,L] <= V then give
Q_beta = V C_Q_beta(y), with V intersect C_Q_beta(y) exactly
Z_alpha intersect Z_gamma. Finiteness is used only inside the local group;
the ambient completion may be infinite.

Alpha remains arbitrary in the earlier rank-one catalogue. This proves the
splitting step in (11.3)(h), not the vanishing of its complementary factor.
SmallPairSplitting treats D10, Sz(2), SU3(2) and PSU3(2); PairDirectFactor
constructs the resulting direct decomposition modulo the two alpha cores.
The large unitary actor, Cartan-invariant opposite-seed omega calculation,
general (11.3)(h)/(11.4), alpha selection and remaining profiles still require
their source arguments.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h), printed pp.170--171, using (5.11), printed p.112.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
open BenderSuzuki.MatrixGroups
private theorem suzuki_omega_pair {m : ℕ} (hm : 0 < m)
    (R T : Sylow 2 (SuzukiMatrixGroup m)) (hne : R ≠ T) :
    omegaCenterIn (R : Subgroup (SuzukiMatrixGroup m)) ⊔ omegaCenterIn (T : Subgroup (SuzukiMatrixGroup m)) = ⊤ := by
  have hd : Disjoint (R : Subgroup (SuzukiMatrixGroup m)) (T : Subgroup (SuzukiMatrixGroup m)) := by
    obtain ⟨S,hS⟩ := suzukiRootSubgroup_isSylow m hm
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) S R
    obtain ⟨t,ht⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) S T
    have hR : (R : Subgroup (SuzukiMatrixGroup m)) = (SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom := by
      rw [←hg,←hS]; rfl
    have hT : (T : Subgroup (SuzukiMatrixGroup m)) = (SuzukiRootSubgroup m).map (MulAut.conj t).toMonoidHom := by
      rw [←ht,←hS]; rfl
    rw [hR,hT]
    exact suzukiRootSubgroup_conjugates_disjoint m hm g t (fun he =>
      hne (Sylow.ext (hR.trans (he.trans hT.symm))))
  rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
    suzuki_omega_center_eq,suzuki_omega_center_eq]
  have hTne : omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup m)) ≠ ⊥ := by
    intro he
    have hh := suzukiSylow_omega_card hm (MulEquiv.refl _) T
    rw [he,card_bot] at hh
    have hp := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : 2*m+1 ≠ 0)
    omega
  obtain ⟨t,ht,ht1⟩ := (omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup m))).bot_or_exists_ne_one.resolve_left hTne
  let := suzukiSylow_omega_elementary hm (MulEquiv.refl _) T
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have htR : t ∉ R := fun hh => ht1 (disjoint_def.mp hd hh (omegaOneAmbient_le _ ht))
  have htN : t ∉ normalizer (R : Set (SuzukiMatrixGroup m)) := by
    intro hn
    have hp : IsPGroup 2 (zpowers t) :=
      (IsElementaryAbelian.zpowers_of_pow_eq_one ht2).isPGroup
    have hi := hp.inf_normalizer_sylow R
    exact htR (hi.le ⟨mem_zpowers t,hn⟩).2
  obtain ⟨e,hR,hB⟩ := suzukiSylow_aligned_equiv hm (MulEquiv.refl _) R
  have htB : e.symm t ∉ SuzukiBorelSubgroup m := by
    intro hh
    apply htN
    rw [←hB]
    simpa only [MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using mem_map_of_mem e.toMonoidHom hh
  have hgen := congrArg (map e.toMonoidHom)
    (suzukiRootSubgroup_omega_sup_zpowers_eq_top m hm (e.symm t) htB)
  rw [Subgroup.map_sup,map_omegaOneAmbient_injective e.toMonoidHom e.injective,hR,
    MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,e.apply_symm_apply,map_top_of_surjective _ e.surjective] at hgen
  exact top_unique (hgen ▸ sup_le le_sup_left ((zpowers_le.mpr ht).trans le_sup_right))

private theorem linear_omega_pair {k : Type*} [Field k] [Finite k] [CharP k 2]
    (R T : Sylow 2 SL(2,k)) (hne : R ≠ T) :
    omegaCenterIn (R : Subgroup SL(2,k)) ⊔ omegaCenterIn (T : Subgroup SL(2,k)) = ⊤ := by
  rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
    sl2_omega_center_eq,sl2_omega_center_eq]
  exact Matrix.SpecialLinearGroup.sylow_sup_eq_top 2 R T hne
private theorem full_pair_actor {D : Type*} [Group D]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* D)
    (hgen : ∀ R T : Sylow 2 D, R ≠ T →
      omegaCenterIn (R : Subgroup D) ⊔ omegaCenterIn (T : Subgroup D) = ⊤) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    ∃ hHK : H ≤ d.localGroup b,
      let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 (d.localGroup b))).comp (inclusion hHK))
      Function.Surjective f ∧ f.ker = (Q (family P) b).subgroupOf H ∧
      ∃ R T : Sylow 2 D, R ≠ T ∧
        ((Z (family P) a).subgroupOf H).map f = omegaCenterIn (R : Subgroup D) ∧
        ((Z (family P) c).subgroupOf H).map f = omegaCenterIn (T : Subgroup D) := by
  let := finite_endpoints h
  let : Finite (d.localGroup b) := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hHK,R,T,hRT,hk,ha,hc',hr⟩ := source_pair_actor_map h hB d hc hb hbc hac Mb
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let K := d.localGroup b
  let q := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hHK)
  let f := e.toMonoidHom.comp q
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRT' : R' ≠ T' := by
    intro he
    exact hRT (Sylow.ext (map_injective e.injective (congrArg Sylow.toSubgroup he)))
  have hker : f.ker = (Q (family P) b).subgroupOf H := by
    rw [←hk]
    ext x
    change e (q x) = 1 ↔ q x = 1
    rw [←e.map_one,e.injective.eq_iff]
  have hmap (A : Subgroup H) (S : Sylow 2 (K ⧸ pCore 2 K))
      (hAS : A.map q = omegaCenterIn (S : Subgroup (K ⧸ pCore 2 K))) :
      A.map f = omegaCenterIn (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup D) := by
    rw [show f = e.toMonoidHom.comp q from rfl,←map_map,hAS,
      NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective]
    rfl
  have hfa := hmap _ R ha
  have hfc := hmap _ T hc'
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,hr,Subgroup.map_sup,
      NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,
      NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective]
    exact hgen R' T' hRT'
  exact ⟨hHK,hsurj,hker,R',T',hRT',hfa,hfc⟩

private theorem full_pair_fixed_preimages {D : Type*} [Group D]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (f : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* D)
    (hf : Function.Surjective f)
    (hk : f.ker = (Q (family P) b).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
    (R T : Sylow 2 D)
    (ha : ((Z (family P) a).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).map f =
      omegaCenterIn (R : Subgroup D))
    (hc' : ((Z (family P) c).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).map f =
      omegaCenterIn (T : Subgroup D))
    (hodd : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (σ : Representation (ZMod 2) D W),
      IsCompl (fixedSpace σ (omegaCenterIn (R : Subgroup D)))
        (fixedSpace σ (omegaCenterIn (T : Subgroup D))) →
      ∀ y : D, Odd (orderOf y) → y ≠ 1 → fixedSpace σ (zpowers y) = ⊥) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∀ y, Odd (orderOf (f y)) → f y ≠ 1 →
      ∀ x ∈ V, (⁅x,(y : G)⁆ ∈ J ↔ x ∈ J) := by
  let := finite_endpoints h
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let D₀ := Q (family P) a ⊓ Q (family P) c
  obtain ⟨hJ,hE,hQ,σ₀,s₀,_⟩ := source_rankOne_pair_section h hB d hc hb hbc hac Ma Mb
  let := hJ
  let := hE
  have hinter : D₀ ⊓ V = J := source_rankOne_pair_core_intersection h hB d hc hb hbc hac Mb
  have hn := source_pair_core_normalizers h (source_critical_one_adjacent hc hb) hbc
  have hHJ : H ≤ normalizer (J : Set G) := by
    rw [←hinter]
    exact (le_inf hn.2.1 hn.2.2.1).trans inf_normalizer_le_normalizer_inf
  have hdisp : ⁅Q (family P) b,V⁆ ≤ J := by
    rw [←hinter]
    exact le_inf (source_rankOne_pair_core_action h hB d hc hb hbc Ma Mb)
      (le_normalizer_iff_commutator_le_right.mp (le_sup_right.trans hn.2.2.1))
  obtain ⟨σ,s,_⟩ := exists_descended_actor H V J s₀.section_le s₀.kernel_le
    hn.2.2.1 hHJ f hf (by
      intro y hy x hx
      have hyker : y ∈ f.ker := hy
      rw [hk] at hyker
      exact hdisp (commutator_mem_commutator hyker hx))
  have hfixed := source_rankOne_pair_fixed_spaces h hB d hc hb hbc Mb f hf hk σ s
  have hJQ : J ≤ Q (family P) b := s.kernel_le.trans (pairSpan_le_core _ _ _)
  have he : J = (Z (family P) a ⊓ Q (family P) b) ⊓ (Z (family P) c ⊓ Q (family P) b) :=
    le_antisymm (le_inf (le_inf inf_le_left hJQ) (le_inf inf_le_right hJQ))
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  have hcompl := s.isCompl_imageSpace (Z (family P) a ⊓ Q (family P) b)
    (Z (family P) c ⊓ Q (family P) b) rfl he
  rw [←hfixed.2.1,←hfixed.2.2,ha,hc'] at hcompl
  let : Finite V := Finite.of_injective (inclusion ((pairSpan_le_core _ _ _).trans (Q_le_stabilizer _ b))) (inclusion_injective _)
  let : Finite (V ⧸ J.subgroupOf V) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  dsimp only
  intro y hy hy1 x hx
  have hz := hodd _ σ hcompl (f y) hy hy1
  have hv := s.fixed_coordinate_iff_commutator_mem y ⟨x,hx⟩
  rw [←hv]
  change σ (f y) (s.coordinates ⟨x,hx⟩).toAdd = (s.coordinates ⟨x,hx⟩).toAdd ↔ _
  rw [←mem_fixedSpace_zpowers_iff,hz,Submodule.mem_bot]
  exact s.coordinates_eq_one_iff ⟨x,hx⟩

/-- Lift a prescribed odd actor and split the beta core. Only the fixed
preimages of this actor are required; its full ambient model is irrelevant. -/
theorem source_pair_coprime_splitting_of_odd_actor {D : Type*} [Group D]
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c)
    (hHK : (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b ≤ d.localGroup b)
    (f : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* D)
    (hf : Function.Surjective f)
    (hk : f.ker = (Q (family P) b).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
    (hJV : Z (family P) a ⊓ Z (family P) c ≤
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))
    (y₀ : D) (hy₀ : Odd (orderOf y₀)) (hy₀1 : y₀ ≠ 1)
    (hfix : ∀ y, f y = y₀ →
      ∀ x ∈ pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b),
        (⁅x,(y : G)⁆ ∈ Z (family P) a ⊓ Z (family P) c ↔
          x ∈ Z (family P) a ⊓ Z (family P) c)) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  let := finite_endpoints h
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let L := Z (family P) a ⊔ Z (family P) c
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let Q₀ := (Q (family P) b).subgroupOf H
  let : Finite H := Finite.of_injective (inclusion (hHK.trans (d.local_le b))) (inclusion_injective _)
  let : Finite L := Finite.of_injective (inclusion (show L ≤ H from le_sup_left)) (inclusion_injective _)
  let j : L →* H := inclusion (show L ≤ H from le_sup_left)
  let fL := f.comp j
  have hj : j.range = L.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨y,he⟩
      change x.val ∈ L
      exact (congrArg Subtype.val he) ▸ y.property
    · exact fun hx => ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
  have hfL : Function.Surjective fL := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,hj]
    have ht : L.subgroupOf H ⊔ Q₀ = ⊤ := by
      rw [←subgroupOf_sup (show L ≤ H from le_sup_left) le_sup_right]
      exact subgroupOf_self H
    have hm := congrArg (map f) ht
    have hz : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [Subgroup.map_sup,show Q₀ = f.ker from hk.symm,hz,sup_bot_eq,
      map_top_of_surjective _ hf] at hm
    exact hm
  obtain ⟨y,hy,hey⟩ := fL.exists_pRegular_lift hfL 2 Nat.prime_two y₀ hy₀.not_two_dvd_nat
  let yH : H := j y
  have hyH : Odd (orderOf yH) := by
    rw [orderOf_injective j (inclusion_injective _) y]
    exact Nat.not_even_iff_odd.mp (fun he => hy he.two_dvd)
  have hyG : Odd (orderOf (y : G)) := by
    rw [Subgroup.orderOf_coe]
    exact Nat.not_even_iff_odd.mp (fun he => hy he.two_dvd)
  have hFy : f yH = y₀ := hey
  have hn := source_pair_core_normalizers h (source_critical_one_adjacent hc hb) hbc
  have hnorm : zpowers yH ≤ normalizer (Q₀ : Set H) := by
    apply zpowers_le.mpr
    exact le_normalizer_comap H.subtype
      (stabilizer_normalizes_Q (family P) b ((hHK.trans (d.local_le b)) yH.property))
  have hp : IsPGroup 2 Q₀ := (isPGroup_pCoreIn 2 (stabilizer (family P) b)).comap_subtype
  have hcop : Nat.Coprime (Nat.card (zpowers yH)) (Nat.card Q₀) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [Nat.card_zpowers,hn]
    exact hyH.coprime_two_right.pow_right n
  have hs := congrArg (map H.subtype)
    (eq_commutator_sup_centralizer_of_solvable_coprime Q₀ (zpowers yH)
      hnorm (@IsNilpotent.to_isSolvable Q₀ _ hp.isNilpotent) hcop)
  have hQH : Q (family P) b ≤ H := le_sup_right
  rw [Subgroup.map_sup,map_commutator,map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hQH,NilesRankOneKernel.centralizer_map_subtype,MonoidHom.map_zpowers,
    ←inf_assoc,inf_eq_left.mpr hQH] at hs
  change Q (family P) b = ⁅Q (family P) b,zpowers (y : G)⁆ ⊔
    (Q (family P) b ⊓ centralizer (zpowers (y : G) : Set G)) at hs
  have hgen : Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers (y : G) : Set G)) := by
    apply le_antisymm ?_ (sup_le (pairSpan_le_core _ _ _) inf_le_left)
    have hyL : zpowers (y : G) ≤ L := zpowers_le.mpr y.property
    have hm : ⁅Q (family P) b,zpowers (y : G)⁆ ≤ V :=
      (commutator_mono (le_refl (Q (family P) b)) hyL).trans hn.2.2.2
    exact hs.le.trans (sup_le (hm.trans le_sup_left) le_sup_right)
  have hJQ : J ≤ Q (family P) b := hJV.trans (pairSpan_le_core _ _ _)
  dsimp only
  have hyG1 : (y : G) ≠ 1 := by
    intro he
    apply hy₀1
    rw [←hFy,show yH = 1 from Subtype.ext he,map_one]
  refine ⟨y,y.property,hyG,hyG1,hgen,le_antisymm ?_ ?_⟩
  · intro x hx
    apply (hfix yH hFy x hx.1).mp
    have hcxy : x*(y:G)=(y:G)*x :=
      (mem_centralizer_iff.mp hx.2 (y:G) (mem_zpowers _)).symm
    change ⁅x,(y:G)⁆ ∈ J
    rw [commutatorElement_def,hcxy,mul_inv_cancel_right,mul_inv_cancel]
    exact J.one_mem
  · exact le_inf ((le_inf inf_le_left hJQ).trans le_sup_left)
      ((inf_le_inf ((source_Z_Q_U h a).1.trans (map_subtype_le _))
          ((source_Z_Q_U h c).1.trans (map_subtype_le _))).trans
        ((le_centralizer_iff.mp hn.1).trans (centralizer_le (zpowers_le.mpr y.property))))

private theorem full_model_pair_coprime_splitting {D : Type*} [Group D]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* D)
    (hgen : ∀ R T : Sylow 2 D, R ≠ T →
      omegaCenterIn (R : Subgroup D) ⊔ omegaCenterIn (T : Subgroup D) = ⊤)
    (hodd : ∀ (R T : Sylow 2 D), R ≠ T →
      ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (σ : Representation (ZMod 2) D W),
      IsCompl (fixedSpace σ (omegaCenterIn (R : Subgroup D)))
        (fixedSpace σ (omegaCenterIn (T : Subgroup D))) →
      ∀ y : D, Odd (orderOf y) → y ≠ 1 → fixedSpace σ (zpowers y) = ⊥)
    (y₀ : D) (hy₀ : Odd (orderOf y₀)) (hy₀1 : y₀ ≠ 1) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  obtain ⟨hHK,hf,hk,R,T,hRT,ha,hc'⟩ := full_pair_actor h hB d hc hb hbc hac Mb e hgen
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 (d.localGroup b))).comp (inclusion hHK))
  have hfix := full_pair_fixed_preimages h hB d hc hb hbc hac Ma Mb f hf hk R T ha hc'
    (hodd R T hRT)
  have hJV := (source_rankOne_pair_core_intersection h hB d hc hb hbc hac Mb).ge.trans inf_le_right
  exact source_pair_coprime_splitting_of_odd_actor h d hc hb hbc hHK f hf hk hJV y₀ hy₀ hy₀1
    (fun y hy => hfix y (hy.symm ▸ hy₀) (fun he => hy₀1 (hy.symm.trans he)))

/-- The coprime splitting used in (11.3)(h), with a linear beta quotient
and every alpha row retained. The odd actor is in the actual center pair. -/
theorem source_linear_pair_coprime_splitting
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,k)) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  let y₀ := Representation.QuadraticFourGroup.TensorClassification.cubicMatrix k
  have hy₀ : orderOf y₀ = 3 := Representation.QuadraticFourGroup.TensorClassification.cubicMatrix_order k
  apply full_model_pair_coprime_splitting h hB d hc hb hbc hac Ma Mb e linear_omega_pair
    _ y₀ (hy₀ ▸ (by decide : Odd (3:ℕ))) (fun he => by simp only [he,orderOf_one] at hy₀; omega)
  intro R T _ W _ _ _ σ hcompl y hy hy1
  rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
    sl2_omega_center_eq,sl2_omega_center_eq] at hcompl
  exact sl2_odd_fixed_eq_bot_of_complement σ R T hcompl y hy (pow_orderOf_eq_one y) hy1

/-- The same literal splitting for every nondegenerate Suzuki beta field,
without selecting linear alpha or postulating a fixed-point-free element. -/
theorem source_suzuki_pair_coprime_splitting
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {m : ℕ} (hm : 0 < m)
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  have hne : SuzukiSplitTorus m ≠ ⊥ := by
    intro he
    have hh := suzukiSplitTorus_card m hm
    rw [he,card_bot] at hh
    have hbig := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega : 2 ≤ 2*m+1)
    norm_num at hbig
    omega
  obtain ⟨y₀,hy₀,hy₀1⟩ := (SuzukiSplitTorus m).bot_or_exists_ne_one.resolve_left hne
  have hyodd : Odd (orderOf y₀) := by
    apply Odd.of_dvd_nat _ ((SuzukiSplitTorus m).orderOf_dvd_natCard hy₀)
    rw [suzukiSplitTorus_card m hm]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by omega : 2*m+1 ≠ 0)) odd_one
  apply full_model_pair_coprime_splitting h hB d hc hb hbc hac Ma Mb e (suzuki_omega_pair hm)
    _ y₀ hyodd hy₀1
  intro R T hRT W _ _ _ σ hcompl y hy hy1
  rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
    suzuki_omega_center_eq,suzuki_omega_center_eq] at hcompl
  exact suzuki_odd_fixed_eq_bot_of_complement hm σ R T hRT hcompl y hy hy1

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
