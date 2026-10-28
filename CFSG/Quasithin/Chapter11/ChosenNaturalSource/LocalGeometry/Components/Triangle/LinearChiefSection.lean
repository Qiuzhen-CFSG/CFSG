module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearPointNormalizer
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.GroupTheory.NoncentralChiefRefinement.MovedChief

/-!
# The original chief section in the linear triangle

The centralizer span U is a normal two-subgroup of KT, so it lies in
O₂(KT). The original Cartan normalizes C_U(X₁). Its two nonzero cubic
displacements lie in this fixed subgroup, which is disjoint from V₁;
therefore both survive under the literal quotient U → U/V₁. The quotient
is elementary abelian by the previously proved Frattini bound.

In J=KXU, choose a maximal normal layer above V₁ in [U,K]V₁.
Perfect-actor commutator idempotence makes K act nontrivially on its
chief section. Since [U,U]≤V₁, U acts trivially there, so its irreducibility
is already irreducibility for the original KX. The normal two-core of
KX acts trivially on this binary simple module. The final theorem descends
the action through the literal KX/O₂(KX) quotient, with the original
carrier, both endpoints, and nontrivial K-action retained.

These are genuine section-selection and action results under the original
chosen-module hypotheses. They do not assume a chief section or a module
recognition witness. Faithfulness of the descended action, the natural/dual
layer comparison, selection of the PGL₃ adjoint extension, and both subsequent
centralizer branches remain to be proved. Common-normal existence and the
final triangle orientations and source assembly also remain open.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, proof of
11.1.2, printed pp.763--764, the cubic displacement and KX-chief-factor steps.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The original span lies in the actual two-core of KT, the source location
of the later KX-chief section. -/
theorem linear_point_span_le_component_join_core
    (f : InvariantFlag (.sl3 m))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K) :
    conjugateSpanBy V (centralizer (f.Vi 0 : Set G)) ≤
      (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hUT := (linear_point_centralizer_span D S m f).2.1
  have hn := (linear_point_centralizer_span_actors D S m f hfix hX hK hLK).1
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hUT) (hUT.trans le_sup_right)
    ((sup_le_sup le_sup_left le_rfl).trans hn)

/-- Both nonzero displacements survive above the literal source point.
The same fixed subgroup and the original Cartan are retained. -/
theorem linear_cubic_displacements_not_le_point
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let C := U ⊓ centralizer (E : Set G)
    ⁅C,X ⊓ K⁆ ≤ C ∧ ⁅C,X⁆ ≤ C ∧
      ¬ ⁅C,X ⊓ K⁆ ≤ f.Vi 0 ∧ ¬ ⁅C,X⁆ ≤ f.Vi 0 ∧ ¬ ⁅U,K⁆ ≤ f.Vi 0 := by
  intro E U C
  let e := (Coordinates.sl3 m).cartanTorusEquiv hX
  let : IsMulCommutative X := .of_comm fun a b => e.injective (by simp only [map_mul,mul_comm])
  have hXcentral : X ≤ centralizer (E : Set G) :=
    X.le_centralizer.trans (centralizer_le inf_le_left)
  have hXE : X ≤ normalizer (centralizer (E : Set G) : Set G) :=
    (hXcentral.trans (Subgroup.centralizer_le_normalizer _)).trans
      (normalizer_le_normalizer_centralizer E)
  have hactors := (linear_point_centralizer_span_actors D S m f hfix hX hK.1 hLK).1
  have hXC : X ≤ normalizer (C : Set G) :=
    (le_inf ((le_sup_right.trans le_sup_left).trans hactors) hXE).trans
      inf_normalizer_le_normalizer_inf
  have hYC : ⁅C,X⁆ ≤ C := le_normalizer_iff_commutator_le_left.mp hXC
  have hKC : ⁅C,X ⊓ K⁆ ≤ C := (commutator_mono le_rfl inf_le_left).trans hYC
  have hdis := (linear_four_original_centralizer_setup D S m f hd hX hcard hmove).2.2.2.2
  obtain ⟨hnK,hnX⟩ := linear_cubic_displacement_of_projective D S m f hd hfix hX hK hLK
    hk hp hcard hmove
  have hnp : ¬ ⁅C,X ⊓ K⁆ ≤ f.Vi 0 := fun h =>
    hnK (bot_unique ((le_inf hKC h).trans hdis.le_bot))
  exact ⟨hKC,hYC,hnp,
    fun h => hnp ((commutator_mono le_rfl inf_le_left).trans h),
    fun h => hnp ((commutator_mono inf_le_left inf_le_right).trans h)⟩

/-- The original elementary section U/V₁ contains both nonzero cubic
displacement images under its literal quotient map. -/
theorem linear_point_quotient_cubic_displacement
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let C := U ⊓ centralizer (E : Set G)
    let B := (f.Vi 0).subgroupOf U
    let : B.Normal := normal_subgroupOf_of_le_normalizer
      ((linear_point_centralizer_span D S m f).2.1.trans (f.invariant 0))
    let π := QuotientGroup.mk' B
    IsElementaryAbelian 2 (U ⧸ B) ∧
      ((⁅C,X ⊓ K⁆).subgroupOf U).map π ≠ ⊥ ∧
      ((⁅C,X⁆).subgroupOf U).map π ≠ ⊥ := by
  intro E U C B hN π
  obtain ⟨_,hUT,hΦ,_⟩ := linear_point_centralizer_span D S m f
  have helem : IsElementaryAbelian 2 (U ⧸ B) :=
    elementary_quotient_of_frattini_le (T.isPGroup'.to_le hUT) B
      (fun u hu => hΦ (mem_map_of_mem U.subtype hu))
  obtain ⟨hKC,hXC,hnK,hnX,_⟩ :=
    linear_cubic_displacements_not_le_point D S m f hd hfix hX hK hLK hk hp hcard hmove
  have hnonzero (Y : Subgroup G) (hYU : Y ≤ U) (hn : ¬ Y ≤ f.Vi 0) :
      (Y.subgroupOf U).map π ≠ ⊥ := by
    intro he
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hh
    apply hn
    intro y hy
    exact hh (show (⟨y,hYU hy⟩ : U) ∈ Y.subgroupOf U from hy)
  exact ⟨helem,hnonzero _ (hKC.trans inf_le_left) hnK,
    hnonzero _ (hXC.trans inf_le_left) hnX⟩


open NoncentralChiefRefinement in
/-- Construct an actual KX-chief section above V₁ inside the source U.
Its binary irreducibility and nontrivial K-action are proved, with the
literal section conjugation and original inclusion of KX retained. -/
theorem linear_point_moved_chief_section
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    ∃ B A : NormalNode J,
      (f.Vi 0).subgroupOf J ≤ B.val ∧ B ⋖ A ∧ A.val ≤ U.subgroupOf J ∧
      IsElementaryAbelian 2 (Section B A) ∧
      (∀ W : Subgroup (Section B A),
        (∀ x : (K ⊔ X : Subgroup G), ∀ w ∈ W,
          sectionAction B A (inclusion (show K ⊔ X ≤ J from le_sup_left) x) w ∈ W) →
          W = ⊥ ∨ W = ⊤) ∧
      ∃ k : K, sectionAction B A
        (inclusion (show K ≤ J from le_sup_left.trans le_sup_left) k) ≠ 1 := by
  intro U J
  have hUT : U ≤ (T : Subgroup G) := (linear_point_centralizer_span D S m f).2.1
  have hZU : f.Vi 0 ≤ U := (D.centralQuotientPreimage_le _).trans (le_conjugateSpanBy _ _)
  have hUJ : U ≤ J := le_sup_right
  have hKJ : K ≤ J := le_sup_left.trans le_sup_left
  have hXN : X ≤ normalizer (f.Vi 0 : Set G) := by
    apply f.cartan_normalizes _ hX 0
    intro i W hW hT
    exact (SL3.flag_inner_unique D S m i W hW hT).trans
      (SL3.flag_inner_unique D S m i (f.space i) (f.dimension i)
        (inf_le_left.trans (f.invariant i))).symm
  have hJN : J ≤ normalizer (f.Vi 0 : Set G) :=
    sup_le (sup_le hK.1.1 hXN) (hUT.trans (f.invariant 0))
  have hactors := (linear_point_centralizer_span_actors D S m f hfix hX hK.1 hLK).1
  have hJU : J ≤ normalizer (U : Set G) :=
    sup_le (le_sup_left.trans hactors) U.le_normalizer
  have hJK : J ≤ normalizer (K : Set G) :=
    hJN.trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  let Z : NormalNode J := ⟨(f.Vi 0).subgroupOf J, normal_subgroupOf_of_le_normalizer hJN⟩
  let R : NormalNode J := ⟨U.subgroupOf J,normal_subgroupOf_of_le_normalizer hJU⟩
  let C : NormalNode J := ⟨K.subgroupOf J,normal_subgroupOf_of_le_normalizer hJK⟩
  let : Group.IsPerfect C.val := (hK.1.2.subgroupOf_of_le hKJ hJN).perfect
  have hR : IsPGroup 2 R.val := (T.isPGroup'.to_le hUT).comap_subtype
  have hCp : IsPPerfect 2 C.val := (pResidual_eq_top_iff 2 C.val).mp (pResidual_eq_top_of_isPerfect 2)
  have hn : ¬ ⁅R.val,C.val⁆ ≤ Z.val := by
    intro hh
    have hmap := map_mono (f := J.subtype) hh
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,map_subgroupOf_eq_of_le hKJ,
      map_subgroupOf_eq_of_le (hZU.trans hUJ)] at hmap
    exact (linear_cubic_displacements_not_le_point D S m f hd hfix hX hK hLK
      hk hp hcard hmove).2.2.2.2 hmap
  obtain ⟨B,A,hZB,hBA,hAR,k,hk⟩ := exists_moved_chief_of_residual_commutator
    Z R C C.val (comap_mono hZU) hR hCp hn C.val.commutator_eq_self
  have hUker : U.subgroupOf J ≤ (sectionAction B A).ker := by
    intro u hu
    apply MulEquiv.ext
    intro w
    induction w using QuotientGroup.induction_on with
    | _ w =>
      change sectionAction B A u (QuotientGroup.mk' (B.val.subgroupOf A.val) w) =
        QuotientGroup.mk' (B.val.subgroupOf A.val) w
      rw [sectionAction_mk]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (u : J) * (w : J) * (u : J)⁻¹ / (w : J) ∈ B.val
      apply hZB
      change (u : G) * ((w : J) : G) * (u : G)⁻¹ / ((w : J) : G) ∈ f.Vi 0
      rw [div_eq_mul_inv]
      change ⁅(u : G),((w : J) : G)⁆ ∈ f.Vi 0
      exact (linear_point_centralizer_span D S m f).2.2.2.1
        (commutator_mem_commutator (show (u : G) ∈ U from hu)
          (show ((w : J) : G) ∈ U from hAR w.property))
  have hgen : (K ⊔ X).subgroupOf J ⊔ U.subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show K ⊔ X ≤ J from le_sup_left) hUJ]
    exact subgroupOf_self J
  have hrange : (sectionAction B A).range =
      ((K ⊔ X).subgroupOf J).map (sectionAction B A) := by
    rw [MonoidHom.range_eq_map,←hgen,Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr hUker,sup_bot_eq]
  refine ⟨B,A,hZB,hBA,hAR,chief_elementary B A hBA (hR.to_le hAR),?_,
    ⟨⟨k,k.property⟩,hk⟩⟩
  intro W hW
  apply chief_irreducible B A hBA W
  intro j w hw
  have hj : sectionAction B A j ∈ ((K ⊔ X).subgroupOf J).map (sectionAction B A) :=
    hrange.le ⟨j,rfl⟩
  obtain ⟨x,hx,he⟩ := hj
  rw [←he]
  exact hW ⟨x,hx⟩ w hw

open NoncentralChiefRefinement in
/-- The selected chief section carries an irreducible action of the actual
KX/O₂(KX), on its original binary carrier, with K still acting nontrivially.
The quotient marking is an equality of representations through the literal
quotient homomorphism. -/
theorem linear_point_chief_quotient_representation
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    let J := (K ⊔ X) ⊔ U
    U ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∃ B A : NormalNode J,
      (f.Vi 0).subgroupOf J ≤ B.val ∧ B ⋖ A ∧ A.val ≤ U.subgroupOf J ∧
      ∃ he : IsElementaryAbelian 2 (Section B A),
      let _ := he
      ∃ ρ : Representation (ZMod 2)
        ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) (Additive (Section B A)),
        Representation.IsIrreducible ρ ∧
        ρ.comp (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))) =
          (binarySectionRepresentation B A).comp
            (inclusion (show K ⊔ X ≤ J from le_sup_left)) ∧
        ∃ k : K, ρ (QuotientGroup.mk' (pCore 2 (K ⊔ X : Subgroup G))
          (inclusion (show K ≤ K ⊔ X from le_sup_left) k)) ≠ 1 := by
  intro U J
  refine ⟨linear_point_span_le_component_join_core D S m f hfix hX hK.1 hLK,?_⟩
  obtain ⟨B,A,hZB,hBA,hAU,he,hirr,k,hk⟩ := linear_point_moved_chief_section D S m f hd
    hfix hX hK hLK hk hp hcard hmove
  let _ := he
  let _ := ((covBy_iff_isChief B A).mp hBA).quotient_nontrivial A.val B.val
  let τ := (binarySectionRepresentation B A).comp
    (inclusion (show K ⊔ X ≤ J from le_sup_left))
  have hτ : Representation.IsIrreducible τ := by
    rw [Representation.IsIrreducible,isSimpleOrder_iff]
    refine ⟨inferInstance,?_⟩
    intro W
    let Q : Subgroup (Section B A) := AddSubgroup.toSubgroup' W.toSubmodule.toAddSubgroup
    rcases hirr Q (fun x w hw => W.apply_mem_toSubmodule x hw) with hz | ht
    · left
      apply bot_unique
      intro w hw
      have hh : w.toMul ∈ Q := hw
      rwa [hz] at hh
    · right
      apply top_unique
      intro w _
      have hh : w.toMul ∈ Q := ht.ge (mem_top _)
      exact hh
  let _ := hτ
  have hcore : pCore 2 (K ⊔ X : Subgroup G) ≤ τ.ker :=
    normal_p_subgroup_le_ker τ _ pCore_isPGroup
  let ρ := quotientOfLEKer τ (pCore 2 (K ⊔ X : Subgroup G)) hcore
  refine ⟨B,A,hZB,hBA,hAU,he,ρ,
    (quotientOfLEKer_irreducible_iff τ _ hcore).mpr hτ,rfl,k,?_⟩
  intro heq
  apply hk
  apply MulEquiv.ext
  intro w
  exact congrArg (fun b : Module.End (ZMod 2) (Additive (Section B A)) =>
    (b (Additive.ofMul w)).toMul) heq

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
