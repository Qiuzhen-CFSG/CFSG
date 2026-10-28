module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairSectionActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoprimeSplitting
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiAllActors

/-!
# The seed-square bound for a nondegenerate Suzuki beta quotient

The two distinct Sylow omega-centers generate the full Suzuki quotient.
The descended pair representation has a nonzero vector and zero global
fixed space, so simplicity makes it faithful. Its quadratic critical-center
actor satisfies the Suzuki square bound. The exact fixed-space quotient
order returns this bound to the original two source indices.

Alpha remains an arbitrary member of the earlier rank-one catalogue. The
parameter-zero Suzuki carrier is not simple and is outside this theorem;
its remaining small-pair calculation is retained by the source owner.

Source: DGS85, Groups and Graphs (1985), (5.12) and (11.3)(g),
printed pp.113--114 and 169--170.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

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
    rw [show f = e.toMonoidHom.comp q from rfl,←Subgroup.map_map,hAS,
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


/-- The full Suzuki pair action gives the source square bound, independently
of alpha selection or nonabelianness of the pair. -/
theorem source_suzuki_seed_square
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m) :
    ((Q (family P) b).relIndex (Z (family P) a))^2 ≤
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) := by
  let := finite_endpoints h
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .suzuki m ⟨eb⟩
  obtain ⟨hHK,hf,hk,R,T,hRT,ha,hc'⟩ := full_pair_actor h hB d hc hb hbc hac Mb eb (suzuki_omega_pair hm)
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let f := eb.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 (d.localGroup b))).comp (inclusion hHK))
  obtain ⟨hJ,hE,σ,s,_,hfixed,hquad,_⟩ := source_pair_section_for_actor h hB d hc hb hbc hac Ma Mb f hf hk
  let := hJ
  let := hE
  let W := Additive (V ⧸ J.subgroupOf V)
  let : Finite V := Finite.of_injective
    (inclusion ((pairSpan_le_core _ _ _).trans (Q_le_stabilizer _ b))) (inclusion_injective _)
  let : Finite (V ⧸ J.subgroupOf V) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨x,hx,hxc⟩ := SetLike.not_le_iff_exists.mp (source_rankOne_seed_escape h hB d hc hb hbc hac Mb).1
  let xV : V := ⟨x,(show Z (family P) a ⊓ Q (family P) b ≤ V from le_sup_left) hx⟩
  let : Nontrivial W := ⟨⟨(s.coordinates xV).toAdd,0,fun he =>
    hxc (((source_Z_Q_U h c).1.trans (map_subtype_le _))
      ((s.coordinates_eq_one_iff xV).mp (Multiplicative.toAdd.injective he)).2)⟩⟩
  let : IsSimpleGroup (SuzukiMatrixGroup m) := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  have hfaith : Function.Injective σ := by
    apply σ.ker_eq_bot_iff.mp
    rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hker | hker
    · exact hker
    · have htop : fixedSpace σ ⊤ = ⊤ := by
        apply top_unique
        intro v _ g
        change σ g v = v
        rw [show σ g = 1 from hker.ge (mem_top g)]
        rfl
      exact (top_ne_bot (htop.symm.trans hfixed)).elim
  have hbound := suzuki_square_bound hm σ hfaith R
    (((Z (family P) a).subgroupOf H).map f)
    (ha ▸ (map_subtype_le _ : omegaCenterIn (R : Subgroup (SuzukiMatrixGroup m)) ≤ R)) hquad
  rw [source_pair_fixed_quotient_card h hB d hc hb hbc Mb f hf hk σ s] at hbound
  have hcard : Nat.card (((Z (family P) a).subgroupOf H).map f) =
      (Q (family P) b).relIndex (Z (family P) a) := by
    rw [←relIndex_ker,hk,relIndex_subgroupOf
      (show Z (family P) a ≤ H from le_sup_left.trans le_sup_left)]
  rwa [hcard] at hbound

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
