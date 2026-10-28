module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.LeftThompson
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleWhole
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.GroupTheory.ElementaryThompsonIntersection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.ThompsonNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Torus
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.Complete

/-!
# The original left Thompson comparison in the Cartan argument

Apply the genuine earlier FF classifier to the original reduced W in LT.
The actual PSL₂ quotient bounds three-rank by one and excludes paired
factors. In the natural row the offender group is perfect, so its image
lies in the original residual image. Lifting through the literal O₂(LT)
puts J(T) in (T ∩ L)O₂(LT) and makes the whole Borel normalize J(T).

The remaining row retains the actual equivariant S₅ quotient of [W,L],
with its precise fixed-space kernel. Its faithful group quotient identifies
L/O₂(L) with A₅; the SL₂ order formula then proves n=2. Thompson movement
is derived from the original A₇ configuration, and the final application
uses the original Hall Cartan and escaping cubic. In the symmetric-five row
the cubic cannot normalize J(T), because its image survives the two-kernel
and the image normalizer has order eight. The completed FF reduction
discharges the configuration premise on the original noncentral inputs.

This completes the left comparison used on p.637. The comparisons with
both A₇ modules, both block exclusions, and the degree-two deduction after
omega-centralization remain with the local Cartan classification owner.
Source: Aschbacher–Smith 5.1.2 and 5.1.13, printed pp.630,637–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

private theorem Input.reduced_centralizer_core
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    centralizer (W.subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let M := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf M
  let U := W.subgroupOf M
  have hr : IsPReduced 2 U := h.reduced_internal
  let := hr.normal
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer h.sylow_normalizes)
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 L)
    (subgroupOfEquivOfLe (show L ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show L ≤ M from le_sup_left)))
  let := h.quotient_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro b hb
    have hh : e b ∈ center (L ⧸ pCore 2 L) := MulEquivClass.apply_mem_center e hb
    rw [h.quotient_center_eq_bot] at hh
    exact e.injective (by simpa only [mem_bot,map_one] using hh)
  have hm : ⁅U,B⁆ ≠ ⊥ := by
    intro hh
    apply h.noncentral
    have he := congrArg (map M.subtype) hh
    have hu : U.map M.subtype = W := map_subgroupOf_eq_of_le h.reduced.1
    have hb : B.map M.subtype = L := map_subgroupOf_eq_of_le le_sup_left
    simpa only [map_commutator,hu,hb,Subgroup.map_bot] using he
  apply reduced_quasisimple_centralizer_eq_pCore U B hr hz hm
  apply isPGroup_quotient_of_sup_eq_top B ((T : Subgroup G).subgroupOf M) T.isPGroup'.comap_subtype
  rw [←subgroupOf_sup (show L ≤ M from le_sup_left) (show (T : Subgroup G) ≤ M from le_sup_right)]
  exact subgroupOf_self M

theorem Input.borel_thompson_of_image
    (h : Input KnownSimple.IsKnownSimple T L W n)
    {Q : Type*} [Group Q]
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Q)
    (hk : q.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (hj : (elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))).map q ≤
      (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map q) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    localBorel T L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let M := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let R := pResidual 2 M
  have hs : (S : Subgroup M).map M.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le le_sup_right
  have hjs : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hs]
  have hi : ((S : Subgroup M) ⊓ R).map M.subtype = (T : Subgroup G) ⊓ L := by
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,hs,h.local_residual_eq]
  have hn := normalizer_intersection_le_normalizer_maxJ_of_image (S : Subgroup M) R q
    (hk.symm ▸ pCore_isPGroup.le_sylow_of_normal S) hj
  refine ⟨?_,?_⟩
  · have hh := map_mono (f := M.subtype)
      (elementaryAbelianMaxJ_le_intersection_sup_ker_of_image (S : Subgroup M) R q
        (hk.symm ▸ pCore_isPGroup.le_sylow_of_normal S) hj)
    simpa only [Subgroup.map_sup,hjs,hi,hk,Subgroup.pCoreIn,M] using hh
  apply sup_le ?_ ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  intro g hg
  have hgm : g ∈ M := (show L ≤ M from le_sup_left) hg.1
  have hgi : (⟨g,hgm⟩ : M) ∈ normalizer (((S : Subgroup M) ⊓ R : Subgroup M) : Set M) := by
    apply mem_normalizer_iff.mpr
    intro x
    have hh := mem_normalizer_iff.mp hg.2 x.val
    rw [←hi] at hh
    change M.subtype x ∈ ((S : Subgroup M) ⊓ R).map M.subtype ↔
      M.subtype ((⟨g,hgm⟩ : M) * x * (⟨g,hgm⟩ : M)⁻¹) ∈
        ((S : Subgroup M) ⊓ R).map M.subtype at hh
    simpa only [Subgroup.mem_map_iff_mem M.subtype_injective] using hh
  have hh := (elementaryAbelianMaxJ (S : Subgroup M)).le_normalizer_map M.subtype
    (mem_map_of_mem M.subtype (hn hgi))
  rwa [hjs] at hh

/-- The original left action supplies the natural Thompson normalizer or an
actual symmetric-five quotient of its moved module. -/
theorem Input.borel_thompson_or_five_section
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    (elementaryAbelianMaxJ (T : Subgroup G) ≤
       ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
     localBorel T L ⊔ (T : Subgroup G) ≤
       normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
    (let M := L ⊔ (T : Subgroup G)
     let U := W.subgroupOf M
     letI := h.reduced_internal.normal
     letI := h.reduced_internal.elementary
     let V := ⁅U,pResidual 2 M⁆
     ∃ p : M →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
       ∃ hk : p.ker = centralizer (V : Set M),
       ∃ f : Additive V →ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
         Function.Surjective f ∧
         (∀ g v, f (NormalElementaryQuotient.representation V p hp hk g v) =
           BinaryPermutation.coreRepresentation (Fin 5) g (f v)) ∧
         f.ker = fixedSpace (NormalElementaryQuotient.representation V p hp hk)
           ((pResidual 2 M).map p)) := by
  classical
  let M := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf M
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  have hSQ : IsSQTK KnownSimple.IsKnownSimple M := by
    have hMM : M ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hMM)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (M.subgroupOf (normalizer (L : Set G))))
  have hns : ¬ Group.IsSolvable M := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable h.maximal_local.1
      (Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (show L ≤ M from le_sup_left)))
  have hSm : (S : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hjm : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hSm]
  have hjS : ¬ elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    intro hc
    apply hj
    rw [←hjm]
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg M.subtype (hc hx ⟨v,h.reduced.1 hv⟩ hv)
  let C := centralizer (U : Set M)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  rcases ChapterE.ThompsonAction.source_nonsolvable_natural_factors
      hSQ S h.local_minimal_parabolic U h.reduced_internal hns hjS with
    ⟨hqs,c,hlin|hfive⟩ | ⟨d,_,_⟩
  · obtain ⟨F,hF⟩ := hlin
    have hall := ChapterE.ThompsonAction.quasisimple_linear_whole_source
      S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData F hF
    let N := offenderSubgroup α
    let e : generalizedFitting N ≃* N := (MulEquiv.subgroupCongr hall.2.1).trans Subgroup.topEquiv
    let := hqs
    let : Group.IsPerfect N := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hres : N ≤ (pResidual 2 M).map q := by
      rw [map_pResidual_of_surjective 2 q hq]
      have hh := map_pResidual_le 2 N.subtype
      rwa [pResidual_eq_top_of_isPerfect 2,←MonoidHom.range_eq_map,range_subtype] at hh
    apply Or.inl
    apply h.borel_thompson_of_image q (hk.trans h.reduced_centralizer_core)
    exact (map_mono (elementaryAbelianMaxJ_sylow_le_top S)).trans (hall.1.le.trans hres)
  · obtain ⟨e⟩ := hfive
    exact Or.inr (ChapterE.ThompsonAction.quasisimple_five_source_marker
      S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData e)
  · have hrank : primeRank 3 M ≤ 1 := by
      rw [←ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
      let e : (pResidual 2 M) ≃* L :=
        (equivMapOfInjective (pResidual 2 M) M.subtype M.subtype_injective).trans
          (MulEquiv.subgroupCongr h.local_residual_eq)
      rw [primeRank_congr 3 e]
      exact Chapter4.Section03.RankOneUniqueness.odd_primeRank_le_one h.linear (by decide)
    let P : Sylow 3 M := Classical.choice inferInstance
    have hr : primeRank 3 (M ⧸ C) ≤ 1 :=
      P.primeRank_quotient_le_one (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hrank) C
    have hy := (primeRank_subgroup_le 3 (offenderSubgroup α)).trans hr
    have hd := d.two_le_three_rank
    change 2 ≤ primeRank 3 (offenderSubgroup α) at hd
    omega

/-- A faithful symmetric-five quotient of the original LT action identifies
both the original L-quotient and its field degree. -/
theorem Input.degree_two_of_symmetric_five
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (p : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5))
    (hp : Function.Surjective p)
    (hk : p.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :
    n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
  let M := L ⊔ (T : Subgroup G)
  let R := pResidual 2 M
  let e : R ≃* L :=
    (equivMapOfInjective R M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr h.local_residual_eq)
  have hkr : (p.subgroupMap R).ker = pCore 2 R := by
    ext r
    simp only [MonoidHom.mem_ker,Subtype.ext_iff]
    change p r.val = 1 ↔ r ∈ pCore 2 R
    change r.val ∈ p.ker ↔ r ∈ pCore 2 R
    rw [hk,pCore_eq_comap_of_normal (H := M) 2 R]
    rfl
  let eR : R ⧸ pCore 2 R ≃* R.map p :=
    (QuotientGroup.quotientMulEquivOfEq hkr.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (p.subgroupMap R) (p.subgroupMap_surjective R))
  have himage : R.map p = alternatingGroup (Fin 5) := ChapterC.SymmetricFive.source_residual_image p hp
  let e5 : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr (pCore 2 R) (pCore 2 L) e (pCore_map_iso 2 e)).symm.trans
      (eR.trans (MulEquiv.subgroupCongr himage))
  refine ⟨?_,⟨e5⟩⟩
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [Nat.card_congr ((Theory.PSL2.sl2QuotientEquiv F).trans (a.symm.trans e5)).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [GorensteinWalter.sl2_card_formula,hF] at hc
  by_contra hn
  have hn3 : 3 ≤ n := by have := h.exponent; omega
  have h8 : 8 ≤ 2^n := by
    have hh := Nat.pow_le_pow_right (by decide : 0<2) hn3
    norm_num at hh
    exact hh
  have h63 : 63 ≤ (2^n)^2-1 := by
    have hh := Nat.mul_self_le_mul_self h8
    simp only [pow_two] at hh ⊢
    omega
  have hh := Nat.mul_le_mul h8 h63
  norm_num at hh
  omega

/-- The natural comparison is forced unless the original left degree is two;
the other alternative retains the literal A₅ quotient isomorphism. -/
theorem Input.borel_thompson_or_degree_two
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    (localBorel T L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
      (n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) := by
  rcases h.borel_thompson_or_five_section hj with hn | hf
  · exact Or.inl hn.2
  · let M := L ⊔ (T : Subgroup G)
    let U := W.subgroupOf M
    let := h.reduced_internal.normal
    let := h.reduced_internal.elementary
    obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := hf
    have hcore : p.ker = pCore 2 M := hk.trans
      ((h.reduced_internal.centralizer_moved_eq U).trans h.reduced_centralizer_core)
    exact Or.inr (h.degree_two_of_symmetric_five p hp hcore)

/-- Thompson movement in the actual A₇ configuration discharges the left
classifier's movement premise. -/
theorem LocalA7Configuration.left_thompson_moves
    {X K : Subgroup G} (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
  intro hj
  have hn : L ≤ normalizer (centralizer (W : Set G) : Set G) :=
    (le_sup_left.trans (reduced_normalizes h.reduced)).trans
      (normalizer_le_normalizer_centralizer W)
  have hc : L ≤ centralizer (W : Set G) := by
    rw [←a.left_thompson]
    exact (commutator_mono le_rfl hj).trans
      (le_normalizer_iff_commutator_le_right.mp hn)
  exact h.noncentral (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))

/-- Source 5.1.13's original noncentral configuration has the natural-left
Thompson normalizer unless the actual left quotient has degree two. -/
theorem LocalA7Configuration.left_thompson_comparison
    {X K : Subgroup G} (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    (localBorel T L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
      (n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :=
  h.borel_thompson_or_degree_two (a.left_thompson_moves h)

/-- In degree greater than two, the original noncentral configuration has
Thompson subgroup contained in (T∩L)O₂(LT), normalized by the whole Borel. -/
theorem LocalA7Configuration.left_natural_thompson_of_degree_gt_two
    {X K : Subgroup G} (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n) (hn : 2 < n) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  rcases h.borel_thompson_or_five_section (a.left_thompson_moves h) with hnat | hf
  · exact hnat
  · let M := L ⊔ (T : Subgroup G)
    let U := W.subgroupOf M
    let := h.reduced_internal.normal
    let := h.reduced_internal.elementary
    obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := hf
    have hcore : p.ker = pCore 2 M := hk.trans
      ((h.reduced_internal.centralizer_moved_eq U).trans h.reduced_centralizer_core)
    have hh := (h.degree_two_of_symmetric_five p hp hcore).1
    omega

/-- The natural-left conclusion applies to the original Hall Cartan and the
actual escaping cubic, with no assumed normalization by either subgroup. -/
theorem LocalA7Configuration.cartan_and_cubic_normalize_thompson
    {A B Y X D K : Subgroup G} (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X D)
    (hn : 2 < n) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      A ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      D ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  obtain ⟨hj,hnorm⟩ := a.left_natural_thompson_of_degree_gt_two h hn
  exact ⟨hj,(sup_le_sup c.left_le le_rfl).trans hnorm,
    (sup_le_sup ((d.cubic_le.trans inf_le_left).trans c.left_le) le_rfl).trans hnorm⟩


/-- A genuine symmetric-five quotient of the original moved module prevents
any original cubic from normalizing J(T). -/
theorem Input.cubic_not_normalizes_thompson_of_five_section
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    {D : Subgroup G} (hDM : D ≤ L ⊔ (T : Subgroup G)) (hDc : Nat.card D = 3)
    (hf : let M := L ⊔ (T : Subgroup G)
      let U := W.subgroupOf M
      letI := h.reduced_internal.normal
      letI := h.reduced_internal.elementary
      let V := ⁅U,pResidual 2 M⁆
      ∃ p : M →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
        ∃ hk : p.ker = centralizer (V : Set M),
        ∃ f : Additive V →ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
          Function.Surjective f ∧
          (∀ g v, f (NormalElementaryQuotient.representation V p hp hk g v) =
            BinaryPermutation.coreRepresentation (Fin 5) g (f v)) ∧
          f.ker = fixedSpace (NormalElementaryQuotient.representation V p hp hk)
            ((pResidual 2 M).map p)) :
    ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let M := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let V := ⁅U,pResidual 2 M⁆
  obtain ⟨p,hp,hk,f,hs,he,hfk⟩ := hf
  have hkU : p.ker = centralizer (U : Set M) :=
    hk.trans (h.reduced_internal.centralizer_moved_eq U)
  have hPmap : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hjmap : (elementaryAbelianMaxJ (P : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hPmap]
  have hjV : ¬ elementaryAbelianMaxJ (P : Subgroup M) ≤ centralizer (V : Set M) := by
    rw [h.reduced_internal.centralizer_moved_eq U]
    intro hc
    apply hj
    rw [←hjmap]
    rintro _ ⟨x,hx,rfl⟩ w hw
    exact congrArg M.subtype (hc hx ⟨w,h.reduced.1 hw⟩ hw)
  have hnot := ChapterC.SymmetricFive.source_cubic_not_normalizes_thompson
    P h.local_minimal_parabolic V (h.reduced_internal.moved U) p hp hk
      ((hkU.trans h.reduced_centralizer_core).symm ▸ pCore_isPGroup)
      f hs he hfk hjV (D.subgroupOf M)
      ((Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv).trans hDc)
  intro hn
  apply hnot
  intro d hd
  apply mem_normalizer_iff.mpr
  intro x
  have hh := mem_normalizer_iff.mp (hn hd) x.val
  rw [←hjmap] at hh
  change M.subtype x ∈ (elementaryAbelianMaxJ (P : Subgroup M)).map M.subtype ↔
    M.subtype (d * x * d⁻¹) ∈ (elementaryAbelianMaxJ (P : Subgroup M)).map M.subtype at hh
  simpa only [Subgroup.mem_map_iff_mem M.subtype_injective] using hh

/-- The actual left FF alternatives are distinguished by the escaping cubic:
the natural row normalizes J(T), whereas the genuine S₅ row does not. -/
theorem LocalA7Configuration.left_thompson_cubic_dichotomy
    {A B Y X D K : Subgroup G} (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X D) :
    (elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
    (n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      A = D ∧ ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  have hj := a.left_thompson_moves h
  rcases h.borel_thompson_or_five_section hj with hnat | hf
  · exact Or.inl hnat
  have hnot := h.cubic_not_normalizes_thompson_of_five_section hj
    (((d.cubic_le.trans inf_le_left).trans c.left_le).trans (inf_le_left.trans le_sup_left))
    d.cubic_card hf
  let M := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf M
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  obtain ⟨p,hp,hk,f,hs,he,hfk⟩ := hf
  have hcore : p.ker = pCore 2 M := hk.trans
    ((h.reduced_internal.centralizer_moved_eq U).trans h.reduced_centralizer_core)
  obtain ⟨hn,h5⟩ := h.degree_two_of_symmetric_five p hp hcore
  exact Or.inr ⟨hn,h5,d.cartan_eq_cubic_of_exponent_eq_two h c hn,hnot⟩

/-- The completed FF reduction supplies the configuration on the original
noncentral source inputs, so no local classification callback is needed for
this left comparison. The right A₇ comparison and block exclusions remain. -/
theorem localCartan_noncentral_left_thompson_dichotomy
    {A B Y X D : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    (elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
    (n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      A = D ∧ ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact a.left_thompson_cubic_dichotomy h c d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
