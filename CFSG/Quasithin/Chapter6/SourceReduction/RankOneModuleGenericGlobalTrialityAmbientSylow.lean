module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityFixedGeometryModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLocalSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralizerBounds
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRootFusion
public import Theory.GroupTheory.PGroup.NormalSubgroups
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityRootPair

/-!
# Ambient Sylow placement and S=T in the triality source row

Transport the genuine fixed-root geometry through the original injective
right-parabolic map. For E=C_T(t), it gives C_S(E) ≤ Z(O²(H)) and E' ≠ 1.
The original cyclic field-action quotient puts E' in S. A finite two-group
has a nontrivial intersection of its center with a nontrivial normal subgroup,
so Z(E) ∩ E' is characteristic, nontrivial and contained in the TI center.
Its normalizer therefore lies in the original right-residual normalizer.

Place E in an actual Sylow two-subgroup R of C_G(t). If E<R, the nilpotent
normalizer condition strictly enlarges E inside R. The preceding normalizer
control puts that enlargement in the already proved local centralizer,
contradicting local maximality. Hence E is genuinely Sylow in C_G(t).
Its strict q^7 upper bound contradicts the ambient q^8 lower bound.
The original Hall-torus splitting supplies such an outer involution whenever
S<T, proving S=T, including q=4 and both original comparison orientations.

Source: Aschbacher--Smith F.4.37--38, printed pp.293--294, and 5.3.3,
p.659 (`refs/quasithin.pdf`). The internal RootPair import reuses the literal
highest-root/center marking; no unmarked factor equivalence is substituted.
Full normalizer realization, full order and ambient recognition remain
obligations of the generic global assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.OuterOdd Triality.Standard.OuterOdd.Coverage
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem transported_involutive {M : Type*} [Group M]
    (P U : Subgroup M) (hUP : U ≤ P) (a : MulAut M) (b : MulAut P)
    (hb : ∀ x : P, (b x).val = a x.val) (haU : ∀ x ∈ U, a x ∈ U)
    (f : P →* G) (hf : Function.Injective f) (t : G) (ht : t^2=1)
    (ha : ∀ x : P, x.val ∈ U → f (b x)=t*f x*t⁻¹) :
    ∀ x ∈ U, a (a x)=x := by
  intro x hx
  let y : P := ⟨x,hUP hx⟩
  have he : b (b y)=y := by
    apply hf
    rw [ha _ (by rw [hb]; exact haU x hx),ha _ hx]
    calc
      t * (t * f y * t⁻¹) * t⁻¹ = (t^2) * f y * (t^2)⁻¹ := by simp only [pow_two]; group
      _ = f y := by rw [ht]; simp
  have hh := congrArg Subtype.val he
  simpa only [hb] using hh

omit [Finite G] in
private theorem transported_fixed_geometry {M : Type*} [Group M]
    (P U Z : Subgroup M) (hUP : U ≤ P) (a : MulAut M) (b : MulAut P)
    (hb : ∀ x : P, (b x).val = a x.val)
    (f : P →* G) (hf : Function.Injective f) (S E : Subgroup G)
    (hS : (U.subgroupOf P).map f=S) (t : G)
    (hSE : S ⊓ centralizer ({t} : Set G) ≤ E)
    (ha : ∀ x : P, x.val ∈ U → f (b x)=t*f x*t⁻¹)
    (hgeom : U ⊓ centralizer ((U ⊓ a.fixedSubgroup : Subgroup M) : Set M) ≤ Z ∧
      _root_.commutator ↥(U ⊓ a.fixedSubgroup) ≠ ⊥) :
    S ⊓ centralizer (E : Set G) ≤ (Z.subgroupOf P).map f ∧ commutator E ≠ ⊥ := by
  let F := U ⊓ a.fixedSubgroup
  let j : F →* P := inclusion ((inf_le_left : F ≤ U).trans hUP)
  have hmem (x : F) : f (j x) ∈ E := by
    apply hSE
    refine ⟨hS ▸ mem_map_of_mem f x.property.1,mem_centralizer_singleton_iff.mpr ?_⟩
    have hbfix : b (j x)=j x := Subtype.ext ((hb _).trans ((MulAut.mem_fixedSubgroup a x.val).mp x.property.2))
    have hh := ha (j x) x.property.1
    rw [hbfix] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  constructor
  · rintro x ⟨hx,hc⟩
    rw [←hS] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    apply mem_map_of_mem f
    apply hgeom.1
    refine ⟨hy,mem_centralizer_iff.mpr ?_⟩
    intro z hz
    have hh : j ⟨z,hz⟩ * y = y * j ⟨z,hz⟩ := by
      apply hf
      rw [map_mul,map_mul]
      exact mem_centralizer_iff.mp hc _ (hmem ⟨z,hz⟩)
    exact congrArg (fun z : P => z.val) hh
  · intro hbot
    let : IsMulCommutative E := (commutator_eq_bot_iff E).mp hbot
    apply hgeom.2
    apply (commutator_eq_bot_iff F).mpr
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    have hh : j x*j y=j y*j x := by
      apply hf
      rw [map_mul,map_mul]
      exact congrArg Subtype.val (mul_comm' (⟨_,hmem x⟩ : E) ⟨_,hmem y⟩)
    exact congrArg (fun z : P => z.val) hh
/-- The original outer involution has a nonabelian Sylow centralizer, whose
centralizer inside S lies in the actual center of O²(H). All fixed-root
geometry is transported through the original right-parabolic comparison. -/
theorem Preparation.triality_outer_fixed_geometry
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val∈D ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htS : t.val∉sourceS L H)
    (htD : t.val∈normalizer (D : Set G)) :
    let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    sourceS L H ⊓ centralizer (E : Set G) ≤ (center (residual H)).map (residual H).subtype ∧
      commutator E ≠ ⊥ := by
  let P := binaryParameters m hm
  have hP : P.prime=2 := rfl
  let Q := parabolic P .arms
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : Q →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  obtain ⟨g,σ,hσ,hact⟩ := d.triality_outer_torus_coefficient_action h hTH hp m hm e hD hmark t ht2 htS htD
  let a := MulAut.conj g.val * coefficientAction P σ
  let gP : Q := inclusion ((torus_le_borel P).trans (borel_le_parabolic P .arms)) g
  let b : MulAut Q := MulAut.conj gP * coefficientParabolic P σ .arms
  have hb (x : Q) : (b x).val = a x.val := rfl
  have haU (x) (hx : x ∈ unipotent P) : a x ∈ unipotent P :=
    (mem_normalizer_iff.mp (borel_le_normalizer_unipotent P hP (torus_le_borel P g.property)) _).mp
      ((coefficient_unipotent P σ).le (mem_map_of_mem _ hx))
  have ha (x : Q) (hx : x.val ∈ unipotent P) : f (b x)=t.val*f x*t.val⁻¹ :=
    (hact x hx).symm
  have hUP : unipotent P ≤ Q := (unipotent_le_borel P).trans (borel_le_parabolic P .arms)
  have ht : t.val^2=1 := congrArg Subtype.val ((orderOf_eq_prime_iff.mp ht2).1)
  have hi := transported_involutive Q (unipotent P) hUP a b hb haU f hf t.val ht ha
  have hgeom := TrialityFixedGeometry.torus_coefficient_fixed_geometry m hm g σ hσ hi
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  have hs := d.triality_right_unipotent_image h hTH P hP e
  have hg := transported_fixed_geometry Q (unipotent P) (highestRoot P) hUP a b hb
    f hf (sourceS L H) E hs t.val
    (inf_le_inf_right _ (sourceS_le_sylow h.sylow_normalizes hTH)) ha hgeom
  have hroot : (highestRoot P).subgroupOf Q = (TrialityRootPair.longHom P hP 2).range := by
    apply map_injective Q.subtype_injective
    rw [map_subgroupOf_eq_of_le ((highestRoot_le_unipotent P hP).trans hUP),
      TrialityRootPair.long_center_range P hP]
  have hZ : ((highestRoot P).subgroupOf Q).map f = (center (residual H)).map (residual H).subtype := by
    rw [hroot,←MonoidHom.range_comp]
    exact (triality_comparison_images d h hTH hp P hP e).1
  exact ⟨hg.1.trans_eq hZ,hg.2⟩
/-- The fixed-root center control gives normalizer control for the actual
centralizer `E = C_T(t)`, with the literal right residual. -/
theorem Preparation.triality_outer_centralizer_normalizer
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t = 2) (htS : t.val ∉ sourceS L H)
    (htD : t.val ∈ normalizer (D : Set G)) :
    normalizer ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  have hgeometry := d.triality_outer_fixed_geometry h hH.1.1.2 hp m hm e hD hmark t ht2 htS htD
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let Z := (center E ⊓ commutator E).map E.subtype
  have hlocal := d.triality_local_structure h hH.1.1.2 hp m hm e
  obtain ⟨b⟩ := hlocal.2.2.2.1
  let eR : (residual H ⧸ pCore 2 (residual H)) ≃*
      Theory.PSL2.Group (ExtensionField (binaryParameters m hm)) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      (localFactorArmsQuotientEquivPSL2 (binaryParameters m hm) rfl)
  let : IsCyclic ((ExtensionField (binaryParameters m hm)) ≃+*
      ExtensionField (binaryParameters m hm)) :=
    Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : CommGroup ((ExtensionField (binaryParameters m hm)) ≃+*
      ExtensionField (binaryParameters m hm)) := IsCyclic.commGroup
  let χ := (residualSylowFieldAction hH.1.1.2 eR).comp
    (inclusion (show E ≤ T from inf_le_left))
  have hder : (commutator E).map E.subtype ≤ sourceS L H := by
    rintro _ ⟨x,hx,rfl⟩
    have hh : inclusion (show E ≤ T from inf_le_left) x ∈
        (residualSylowFieldAction hH.1.1.2 eR).ker :=
      Abelianization.commutator_subset_ker χ hx
    rw [d.residual_sylow_field_kernel h hH.1.1.2
      (d.triality_sourceS_le_factors h hH.1.1.2 hp m hm (Or.inr ⟨e⟩)) eR] at hh
    exact hh
  have htop : Z ≠ ⊥ := by
    let : Nontrivial (commutator E) := (nontrivial_iff_ne_bot _).mpr hgeometry.2
    let : Fact (IsPGroup 2 E) := ⟨T.isPGroup'.to_le inf_le_left⟩
    obtain ⟨x,hx,hxc⟩ := exists_nontrivial_center_mem_normal (p := 2) (commutator E)
    intro hbot
    have hz : x.val.val ∈ Z := mem_map_of_mem E.subtype ⟨hxc,x.property⟩
    rw [hbot,mem_bot] at hz
    exact hx (Subtype.ext (Subtype.ext hz))
  have hZ : Z ≤ (center (residual H)).map (residual H).subtype := by
    apply le_trans ?_ hgeometry.1
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hder (mem_map_of_mem E.subtype hx.2), ?_⟩
    exact mem_centralizer_iff.mpr (fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hx.1 ⟨y,hy⟩))
  have hTI := d.triality_right_center_fusion h hH hp m hm (Or.inr ⟨e⟩)
  exact (normalizer_le_normalizer_characteristic_image E (center E ⊓ commutator E)).trans
    ((hTI.2.1.normalizer_le_of_ne_bot htop hZ).trans_eq hTI.2.2)

/-- C_T(t) is an actual Sylow two-subgroup of the full ambient centralizer.
The normalizer condition is applied in a Sylow subgroup of C_G(t), then
TI-center control places the enlarged normalizer in the proved local group. -/
theorem Preparation.triality_outer_centralizer_ambient_sylow
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val∈D ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htS : t.val∉sourceS L H)
    (htD : t.val∈normalizer (D : Set G)) :
    let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    ∃ R : Sylow 2 (centralizer ({t.val} : Set G)),
      (R : Subgroup (centralizer ({t.val} : Set G))).map (centralizer ({t.val} : Set G)).subtype = E := by
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let C := centralizer ({t.val} : Set G)
  have hEC : E ≤ C := inf_le_right
  have hN := d.triality_outer_centralizer_normalizer h hH hp m hm e hD hmark t ht2 htS htD
  obtain ⟨P,hP⟩ := ((T.isPGroup'.to_le (show E ≤ T from inf_le_left)).comap_subtype
    (K := C)).exists_le_sylow
  let R := (P : Subgroup C).map C.subtype
  have hER : E ≤ R := by
    rw [←map_subgroupOf_eq_of_le hEC]
    exact map_mono hP
  refine ⟨P,?_⟩
  change R=E
  by_contra hneq
  have hR : IsPGroup 2 R := P.isPGroup'.map C.subtype
  let : Group.IsNilpotent R := hR.isNilpotent
  have hproper : E.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
    intro hRE
    exact hneq (le_antisymm hRE hER)
  obtain ⟨u,huN,huE⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (E.subgroupOf R) hproper)
  let V := (normalizer (E.subgroupOf R : Set R)).map R.subtype
  have hEV : E ≤ V := by
    intro x hx
    exact ⟨⟨x,hER hx⟩,le_normalizer hx,rfl⟩
  have hVstrict : E < V := lt_of_le_of_ne hEV (by
    intro heq
    have hu : u.val ∈ V := mem_map_of_mem R.subtype huN
    rw [←heq] at hu
    exact huE hu)
  have hVN : V ≤ normalizer (E : Set G) := by
    rw [←map_subgroupOf_eq_of_le hER]
    exact (E.subgroupOf R).le_normalizer_map R.subtype
  have hVC : V ≤ C := (map_subtype_le _).trans (map_subtype_le _)
  have hV : V = E := d.triality_outer_centralizer_local_maximal h hH.1.1.2 hp m hm e
    hD hmark t ht2 htD V ((hR.to_subgroup _).map _) hEV (le_inf (hVN.trans hN) hVC)
  exact (ne_of_lt hVstrict) hV.symm

/-- In every prepared triality comparison the original source core is all of T.
An outer involution would have an ambient-centralizer Sylow of order <q^7,
contradicting the already proved q^8 lower bound. The original source S,
both whole-overlap squares and the two possible orientations are retained. -/
theorem Preparation.triality_sourceS_eq_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    sourceS L H = (T : Subgroup G) := by
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hH.1.1.2 hp _ rfl he).elim
  obtain ⟨e⟩ := he
  by_contra hne
  obtain ⟨D,hD,_,hmark,_,t,ht2,htS,htD,_⟩ :=
    d.triality_exists_outer_involution h hH.1.1.2 hp m hm e hne
  obtain ⟨R,hR⟩ := d.triality_outer_centralizer_ambient_sylow h hH hp m hm e hD hmark t ht2 htS htD
  have hu := (d.triality_outer_involution_centralizer_lt h hH.1.1.2 hp m hm e hD hmark t ht2 htS htD).2
  have hl := d.triality_involution_centralizer_sylow_lower_bound h hH hp m hm (Or.inr ⟨e⟩)
    t.val ((Subgroup.orderOf_coe t).trans ht2) R
  have hc := congrArg (fun K : Subgroup G => Nat.card K) hR
  rw [card_map_of_injective (centralizer ({t.val} : Set G)).subtype_injective] at hc
  rw [hc] at hl
  exact (not_lt_of_ge (Nat.pow_le_pow_right (by have := (binaryParameters m hm).q_ge_two; omega)
    (by decide : 7≤8))) (hl.trans_lt hu)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
