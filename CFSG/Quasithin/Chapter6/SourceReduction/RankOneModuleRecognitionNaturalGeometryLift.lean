module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryTransvection
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.PSL5Two.UniversalCover

/-!
# Central covers and ambient lifts of the reduced transvection action

For the actual closure P = ⟨E^I⟩ in the odd escaping configuration, the
kernel of its action on W/⟨z⟩ is central modulo O₂(P). The additional
kernel on passing to W/Z_S has exponent two: I fixes Z_S, so it fixes
both the kernel and quotient of this elementary abelian module. Core
transport therefore constructs a central surjection P/O₂(P) onto the
literal reduced image on W/Z_S. The moving actor retains its order,
which is two or four; no claim of core vanishing on W/⟨z⟩ is used.

Since P is normal in I = C_G(Z_S), itself normal in N_G(Z_S), its intrinsic
two-core quotient embeds subnormally in N_G(Z_S)/O₂(N_G(Z_S)). The
solvable residual of a component preimage under the central surjection
is quasisimple, hence is a genuine component after this embedding. Both
maps are retained on representatives, as is the induced equivalence of
the simple central quotients.

The original cubic excludes large alternating central quotients, including
the possible triple covers. The binary degree-four case is A₈; universality
of the identity cover of PSL₅(2) removes the center premise in degree five.
These exclusions apply to the lifted components of the actual reduced image.
The quotient-action and core calculations reuse the arguments of the
NaturalGeometryClosure and NaturalGeometryReduced modules.

The classified factors still need their residuals identified as these
components and their full lifts assembled, including the solvable S₃ factors.
The cubic normalization, parabolic/amalgam contradiction, initial 6.1.4–5
and remaining escape geometry stay with qt-d-1222-rankone-recognition-natural,
which owns unconditional 6.1.27. This module does not assert that theorem.
Source: Aschbacher–Smith 6.1.19, pp.674–675; A.3.18, pp.51–53;
GLS3, Theorem 5.2.3 and §6.1 for the reused central-cover calculations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorLift

private theorem central_core_image
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hk : ⁅(⊤ : Subgroup A), f.ker⁆ ≤ pCore 2 A) :
    (pCore 2 A).map f = pCore 2 B := by
  let Q := pCore 2 A
  let N := Q.map f
  let : N.Normal := Normal.map inferInstance f hf
  let q := QuotientGroup.mk' Q
  let b := QuotientGroup.mk' N
  let a := QuotientGroup.map Q N f (le_comap_map f Q)
  have ha : Function.Surjective a :=
    QuotientGroup.map_surjective_of_surjective Q N f
      ((QuotientGroup.mk'_surjective N).comp hf) (le_comap_map f Q)
  have hcentral : f.ker.map q ≤ center (A ⧸ Q) := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective Q),
      ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [commutator_comm]
  have hak : a.ker ≤ center (A ⧸ Q) := by
    rw [QuotientGroup.ker_map]
    change ((Q.map f).comap f).map q ≤ _
    rw [comap_map_eq, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    exact hcentral
  have hc : pCore 2 (B ⧸ N) = ⊥ := by
    have he := a.map_pCore_of_central_kernel (p := 2) ha hak
    rw [pCore_quotient_pCore_eq_bot, Subgroup.map_bot] at he
    exact he.symm
  apply le_antisymm
  · exact le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  have hm : (pCore 2 B).map b ≤ pCore 2 (B ⧸ N) :=
    le_sSup ⟨Normal.map inferInstance b (QuotientGroup.mk'_surjective N),pCore_isPGroup.map b⟩
  have he : (pCore 2 B).map b = ⊥ := bot_unique (hc ▸ hm)
  simpa only [b,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he

/-- The intrinsic two-core quotient of a subnormal subgroup embeds in the
ambient two-core quotient, with the original quotient maps. -/
private theorem subnormal_embedding
    {N : Type*} [Group N] [Finite N] (P : Subgroup N) (hP : P.IsSubnormal) :
    ∃ j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N),
      Function.Injective j ∧ j.range.IsSubnormal ∧
      ∀ p, j (QuotientGroup.mk' (pCore 2 P) p) = QuotientGroup.mk' (pCore 2 N) p := by
  let f := (QuotientGroup.mk' (pCore 2 N)).comp P.subtype
  have hk : f.ker = pCore 2 P := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hP).symm
  let j := QuotientGroup.lift (pCore 2 P) f hk.ge
  have he (p : P) : j (QuotientGroup.mk' (pCore 2 P) p) = f p := rfl
  have hj : Function.Injective j := by
    rw [←MonoidHom.ker_eq_bot_iff,QuotientGroup.ker_lift,hk]
    exact QuotientGroup.map_mk'_self _
  have hr : j.range = P.map (QuotientGroup.mk' (pCore 2 N)) := by
    have hh : f.range = j.range := by
      change (j.comp (QuotientGroup.mk' (pCore 2 P))).range = _
      rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
        ←MonoidHom.range_eq_map]
    rw [←hh,MonoidHom.range_comp,range_subtype]
  exact ⟨j,hj,hr ▸ hP.map (QuotientGroup.mk'_surjective _),he⟩

/-- A component lifts through a central surjection to a genuine component,
with the image map and its central kernel retained. -/
private theorem component_lift
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (D : Subgroup B) (hD : IsComponent B D) :
    ∃ C : Subgroup A, IsComponent A C ∧ C.map f = D := by
  let : IsMulCommutative f.ker := ⟨⟨fun a b =>
    Subtype.ext ((mem_center_iff.mp (hk a.property) b).symm)⟩⟩
  obtain ⟨hC,hm⟩ := cComponent_residual_preimage f hf hD.isCComponent
  let C := (solvableResidual (D.comap f)).map (D.comap f).subtype
  let := hC.perfect
  let : IsQuasisimple (C.map f) := hm.symm ▸ hD.2
  let F : PerfectCentralCovering.Cover C (C.map f) := {
    toMonoidHom := f.subgroupMap C
    surjective := f.subgroupMap_surjective C
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      have hxk : (x : A) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hk hxk) y) }
  exact ⟨C,⟨hC.subnormal,F.isQuasisimple⟩,hm⟩



/-- Passing from an elementary abelian module to a quotient fixed on the
kernel preserves the central-cover description after removing the two-core. -/
private theorem quotient_action_central_cover
    {P X Y : Type*} [Group P] [Finite P] [CommGroup X] [Finite X]
    [Group Y] [Finite Y]
    (f : P →* MulAut X) (g : P →* MulAut Y) (q : X →* Y)
    (he : ∀ p x, q (f p x) = g p (q x))
    (hfix : ∀ p x, x ∈ q.ker → f p x = x)
    (hexp : ∀ x : X, x ^ 2 = 1)
    (hk : ⁅(⊤ : Subgroup P),f.ker⁆ ≤ pCore 2 P)
    (hc : pCore 2 P ≤ g.ker) :
    ∃ φ : (P ⧸ pCore 2 P) →* g.range,
      Function.Surjective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
      (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
      pCore 2 g.range = ⊥ := by
  have hkf : ⁅(⊤ : Subgroup P),f.rangeRestrict.ker⁆ ≤ pCore 2 P := by
    simpa only [MonoidHom.ker_rangeRestrict] using hk
  have hcore := central_core_image f.rangeRestrict f.rangeRestrict_surjective hkf
  have himage : IsPGroup 2 (g.ker.map f.rangeRestrict) := by
    intro k
    obtain ⟨p,hp,hpk⟩ := k.property
    have hgp : g p = 1 := hp
    have hdisp (x : X) : f p x / x ∈ q.ker := by
      change q (f p x / x) = 1
      rw [map_div,he,hgp,MulAut.one_apply,div_self']
    have hsq (x : X) : f p (f p x) = x := by
      have hh := hfix p (f p x / x) (hdisp x)
      rw [map_div] at hh
      have hm := div_eq_iff_eq_mul.mp hh
      rw [hm]
      have hh2 := hexp (f p x)
      have hx2 := hexp x
      simp only [pow_two] at hh2 hx2
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      rw [div_eq_mul_inv,hxi]
      calc
        f p x * x * f p x = (f p x * f p x) * x := by ac_rfl
        _ = x := by rw [hh2,one_mul]
    refine ⟨1,Subtype.ext (Subtype.ext ?_)⟩
    change ((k : f.range) : MulAut X)^(2^1)=1
    rw [←hpk]
    ext x
    exact hsq x
  have hle : g.ker ≤ pCore 2 P ⊔ f.ker := by
    have hm : g.ker.map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Normal.map inferInstance _ f.rangeRestrict_surjective,himage⟩
    rw [←hcore] at hm
    have hh := map_le_iff_le_comap.mp hm
    simpa only [comap_map_eq,MonoidHom.ker_rangeRestrict] using hh
  let φ := QuotientGroup.lift (pCore 2 P) g.rangeRestrict
    (by simpa only [MonoidHom.ker_rangeRestrict] using hc)
  have hs : Function.Surjective φ := by
    intro y
    obtain ⟨p,rfl⟩ := g.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk' (pCore 2 P) p,rfl⟩
  have hcentral : φ.ker ≤ center (P ⧸ pCore 2 P) := by
    rw [QuotientGroup.ker_lift,MonoidHom.ker_rangeRestrict]
    have hm := map_mono (f := QuotientGroup.mk' (pCore 2 P)) hle
    rw [Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq] at hm
    apply hm.trans
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [←map_top_of_surjective (QuotientGroup.mk' (pCore 2 P)) (QuotientGroup.mk'_surjective _),
      ←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    rwa [commutator_comm]
  refine ⟨φ,hs,hcentral,fun _ => rfl,?_⟩
  have hh := φ.map_pCore_of_central_kernel (p := 2) hs hcentral
  rw [pCore_quotient_pCore_eq_bot,Subgroup.map_bot] at hh
  exact hh.symm

/-- Component lifts retain subnormality under the marked ambient embedding. -/
private theorem component_lift_ambient
    {A B N : Type*} [Group A] [Finite A] [Group B] [Finite B] [Group N]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (j : A →* N) (hj : Function.Injective j) (hn : j.range.IsSubnormal)
    (D : Subgroup B) (hD : IsComponent B D) :
    ∃ C : Subgroup A, IsComponent A C ∧ C.map f = D ∧
      IsComponent N (C.map j) ∧
      Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) := by
  obtain ⟨C,hC,hm⟩ := component_lift f hf hk D hD
  let := hC.2
  let e : C ≃* C.map j :=
    MulEquiv.ofBijective (j.subgroupMap C)
      ⟨fun a b hh => Subtype.ext (hj (congrArg Subtype.val hh)),j.subgroupMap_surjective C⟩
  have hcn : (C.map j).IsSubnormal := by
    have hh := (hC.1.map j.rangeRestrict_surjective).trans' hn
    simpa only [map_map,MonoidHom.subtype_comp_rangeRestrict] using hh
  let F : PerfectCentralCovering.Cover C (C.map f) := {
    toMonoidHom := f.subgroupMap C
    surjective := f.subgroupMap_surjective C
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      have hxk : (x : A) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hk hxk) y) }
  refine ⟨C,hC,hm,⟨hcn,IsQuasisimple.of_mulEquiv e⟩,?_⟩
  let F' : PerfectCentralCovering.Cover (C.map j) D := {
    toMonoidHom := (MulEquiv.subgroupCongr hm).toMonoidHom.comp
      (F.toMonoidHom.comp e.symm.toMonoidHom)
    surjective := (MulEquiv.subgroupCongr hm).surjective.comp (F.surjective.comp e.symm.surjective)
    isPerfect := IsQuasisimple.of_mulEquiv e |>.toIsPerfect
    ker_le_center := by
      intro x hx
      have hxk : e.symm x ∈ F.toMonoidHom.ker := by
        apply (MulEquiv.subgroupCongr hm).injective
        exact (MonoidHom.mem_ker.mp hx).trans ((MulEquiv.subgroupCongr hm).map_one.symm)
      exact mem_center_iff.mpr fun y => e.symm.injective (by
        simpa only [map_mul] using mem_center_iff.mp (F.ker_le_center hxk) (e.symm y)) }
  exact ⟨F'.quotientCenterEquiv⟩


/-- The actual closure in the centralizer is subnormal in the line normalizer. -/
private theorem centralizer_span_subnormal {G : Type*} [Group G]
    (Z E : Subgroup G) (hE : E ≤ centralizer (Z : Set G)) :
    ((conjugateSpanBy E (centralizer (Z : Set G))).subgroupOf
      (normalizer (Z : Set G))).IsSubnormal := by
  let I := centralizer (Z : Set G)
  let N := normalizer (Z : Set G)
  let P := conjugateSpanBy E I
  have hPI : P ≤ I := conjugateSpanBy_le_self hE
  have hIN : I ≤ N := Subgroup.centralizer_le_normalizer _
  let : (P.subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy E I)
  have hp : (P.subgroupOf I).IsSubnormal := Normal.isSubnormal inferInstance
  have hi : (I.subgroupOf N).IsSubnormal := Normal.isSubnormal inferInstance
  apply IsSubnormal.trans (subgroupOf_mono N hPI) _ hi
  let e := subgroupOfEquivOfLe hIN
  have hm := hp.map (f := e.symm.toMonoidHom) e.symm.surjective
  convert hm using 1
  ext x
  constructor
  · intro hx
    exact mem_map.mpr ⟨e x,hx,e.symm_apply_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    exact hy


/-- The same embedding written using an ambient subgroup and its literal inclusion. -/
private theorem relative_embedding {G : Type*} [Group G] [Finite G]
    (P N : Subgroup G) (hPN : P ≤ N) (hs : (P.subgroupOf N).IsSubnormal) :
    ∃ j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N),
      Function.Injective j ∧ j.range.IsSubnormal ∧
      ∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
        QuotientGroup.mk' (pCore 2 N) (inclusion hPN p) := by
  obtain ⟨j,hj,hn,he⟩ := subnormal_embedding (P.subgroupOf N) hs
  let e := (subgroupOfEquivOfLe hPN).symm
  let E := QuotientGroup.congr (pCore 2 P) (pCore 2 (P.subgroupOf N)) e (pCore_map_iso 2 e)
  have hr : (j.comp E.toMonoidHom).range = j.range := by
    rw [MonoidHom.range_comp,show E.toMonoidHom.range = ⊤ from
      MonoidHom.range_eq_top.mpr E.surjective,←MonoidHom.range_eq_map]
  refine ⟨j.comp E.toMonoidHom,hj.comp E.injective,hr ▸ hn,?_⟩
  intro p
  change j (E (QuotientGroup.mk' (pCore 2 P) p)) = _
  change j (QuotientGroup.mk' (pCore 2 (P.subgroupOf N)) (e p)) = _
  exact he (e p)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorLift

private theorem quotient_action_kernel
    {G : Type*} [Group G] (I W Z : Subgroup G)
    (hIW : I ≤ normalizer (W : Set G)) (hIZ : I ≤ Subgroup.normalizer (Z : Set G))
    (hN : (Z.subgroupOf W).Normal) :
    let := hN
    ∀ ρ : I →* MulAut (W ⧸ Z.subgroupOf W),
    (∀ i : I, ∀ w : W,
      ρ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
        QuotientGroup.mk' (Z.subgroupOf W)
          ⟨(i : G) * (w : G) * (i : G)⁻¹,
            (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) →
    ρ.ker = (commutatorPreimage I W Z).subgroupOf I := by
  let := hN
  dsimp only
  intro ρ he
  ext i
  change ρ i = 1 ↔ (i : G) ∈ commutatorPreimage I W Z
  rw [mem_commutatorPreimage_iff I W Z hIZ]
  constructor
  · intro hi
    refine ⟨i.property,fun w hw => ?_⟩
    have hh := congrArg (fun f : MulAut (W ⧸ Z.subgroupOf W) =>
      f (QuotientGroup.mk' (Z.subgroupOf W) ⟨w,hw⟩)) hi
    rw [he] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh
    change (i : G) * w * (i : G)⁻¹ / w ∈ Z at hz
    simpa only [commutatorElement_def,div_eq_mul_inv] using hz
  · rintro ⟨_,hc⟩
    ext w
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) w
    rw [he]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (i : G) * (w : G) * (i : G)⁻¹ / (w : G) ∈ Z
    simpa only [commutatorElement_def,div_eq_mul_inv] using hc w w.property

private theorem actor_card_of_kernel_lines
    {G A B : Type*} [Group G] [Group A] [Group B]
    (I W E Z Z' D : Subgroup G)
    (hIZ : I ≤ normalizer (Z : Set G)) (hID : I ≤ normalizer (D : Set G))
    (hinter : Z ⊓ Z' = D) (hcomm : ⁅E,W⁆ ≤ Z')
    (ρ : I →* A) (σ : I →* B)
    (hker : ρ.ker = (commutatorPreimage I W D).subgroupOf I)
    (hσker : σ.ker = (commutatorPreimage I W Z).subgroupOf I)
    (hkerle : ρ.ker ≤ σ.ker) :
    Nat.card ((E.subgroupOf I).map σ) = Nat.card ((E.subgroupOf I).map ρ) := by
  have hsame : σ.ker.subgroupOf (E.subgroupOf I) = ρ.ker.subgroupOf (E.subgroupOf I) := by
    apply le_antisymm
    · intro e he
      change (e : I) ∈ ρ.ker
      rw [hker]
      apply (mem_commutatorPreimage_iff I W D hID _).mpr
      refine ⟨(e : I).property,fun w hw => ?_⟩
      rw [←hinter]
      have heZ : ((e : I) : G) ∈ commutatorPreimage I W Z := by
        change (e : I) ∈ σ.ker at he
        rwa [hσker] at he
      exact ⟨(mem_commutatorPreimage_iff I W Z hIZ _).mp heZ |>.2 w hw,
        hcomm (commutator_mem_commutator e.property hw)⟩
    · exact subgroupOf_mono _ hkerle
  have hcard : Nat.card ((E.subgroupOf I).map σ) = Nat.card ((E.subgroupOf I).map ρ) := by
    rw [←relIndex_ker,←relIndex_ker]
    exact congrArg Subgroup.index hsame
  exact hcard

open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
/-- In the original normalizer quotient, even the exceptional triple covers
cannot have an alternating central quotient of degree at least six. -/
theorem natural_four_quotient_component_not_alternating_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hK : IsComponent _ K) {m : ℕ} (hm : 6 ≤ m) :
    ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin m)) := by
  rintro ⟨e⟩
  let := hK.2
  have hodd := GLS3.Chapter5.OddCentralCovers.component_center_odd
    (pCore_quotient_pCore_eq_bot 2) K hK
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives m (by omega) e hodd with
      hc | ⟨hm,hc⟩
  · exact natural_four_quotient_component_not_alternating h hnat K hK hm
      ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne m e hc⟩
  · have hz : Nonempty (center K ≃* Multiplicative (ZMod 3)) :=
      ⟨mulEquivOfPrimeCardEq hc (by simp)⟩
    apply natural_four_quotient_component_not_alternating_cover h hnat K hK
    rcases hm with rfl | rfl
    · exact Or.inl ⟨inferInstance,hz,⟨e⟩⟩
    · exact Or.inr ⟨inferInstance,hz,⟨e⟩⟩

/-- A central cover of the binary degree-five group has no kernel. The
conclusion retains the actual surjection, by universality of the identity cover. -/
private theorem five_cover_injective {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (f : A →* Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))
    (hf : Function.Surjective f) : Function.Injective f := by
  let := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple (ZMod 2)
  let c : Covering A (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    { toMonoidHom := f, surjective := hf }
  have hu := Theory.SpecificGroups.PSL5Two.UniversalCover.field_identity_isUniversal
    (ZMod 2) (by simp)
  let s := hu.lift c
  have he := hu.lift_fac c
  intro x y hxy
  obtain ⟨a,rfl⟩ := s.surjective x
  obtain ⟨b,rfl⟩ := s.surjective y
  have ha : f (s a) = a := congrArg (fun k => k a) he
  have hb : f (s b) = b := congrArg (fun k => k b) he
  have hab : a = b := ha.symm.trans (hxy.trans hb)
  exact congrArg s hab

/-- Binary degree-four and degree-five central quotients are excluded with
no premise on the center of the lifted component. -/
theorem natural_four_quotient_component_not_binary_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hK : IsComponent _ K) {m : ℕ} (hm : m = 4 ∨ m = 5) :
    ¬ Nonempty ((K ⧸ center K) ≃* BinaryLinear.OuterCyclic.LinearGroup m) := by
  rintro ⟨e⟩
  rcases hm with rfl | rfl
  · exact natural_four_quotient_component_not_alternating_quotient h hnat K hK
      (by decide : 6 ≤ 8)
      ⟨(e.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).symm).trans
        Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8⟩
  · let := hK.2
    let eP := e.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)).symm
    let f := eP.toMonoidHom.comp (QuotientGroup.mk' (center K))
    have hf : Function.Surjective f := eP.surjective.comp (QuotientGroup.mk'_surjective _)
    let eK := (MulEquiv.ofBijective f ⟨five_cover_injective f hf,hf⟩).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))
    exact natural_four_quotient_component_not_binary_large h hnat K hK (Or.inr rfl) ⟨eK⟩

private theorem lifted_component_sieve
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (φ : A →* B) (hφ : Function.Surjective φ) (hc : φ.ker ≤ center A)
    (j : A →* (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hj : Function.Injective j) (hjn : j.range.IsSubnormal)
    (D : Subgroup B) (hD : IsComponent B D) :
    ∃ C : Subgroup A, IsComponent A C ∧ C.map φ = D ∧
      IsComponent _ (C.map j) ∧
      Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧
      C.map j ≤ ((Escape.I (T : Subgroup G) L R).subgroupOf
        (Escape.H (T : Subgroup G) L R)).map (QuotientGroup.mk' _) ∧
      (∀ m, 6 ≤ m → ¬ Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin m))) ∧
      (∀ m, m = 4 ∨ m = 5 →
        ¬ Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup m)) := by
  obtain ⟨C,hC,hm,hCj,⟨e⟩⟩ :=
    NaturalFactorLift.component_lift_ambient φ hφ hc j hj hjn D hD
  let := hCj.2
  refine ⟨C,hC,hm,hCj,⟨e⟩,
    natural_four_quotient_perfect_le_centralizer h hnat (C.map j),
    ?_,?_⟩
  · rintro m hm ⟨eD⟩
    exact natural_four_quotient_component_not_alternating_quotient h hnat (C.map j)
      hCj hm ⟨e.trans eD⟩
  · rintro m hm ⟨eD⟩
    exact natural_four_quotient_component_not_binary_quotient h hnat (C.map j)
      hCj hm ⟨e.trans eD⟩

namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- The reduced action on the literal W/Z_S has a central cover by P/O₂(P).
That covering group embeds subnormally in the actual normalizer quotient.
Every ordinary component therefore lifts, retaining both original maps. -/
theorem exists_ambient_reduced_component_lifts
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      letI := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
        IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W) ∧
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Surjective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧
          ∀ D : Subgroup g.range, IsComponent g.range D →
            ∃ C : Subgroup (P ⧸ pCore 2 P), IsComponent _ C ∧ C.map φ = D ∧
              IsComponent (N ⧸ pCore 2 N) (C.map j) ∧
              Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧
              C.map j ≤ (I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) ∧
              (∀ m, 6 ≤ m → ¬ Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin m))) ∧
              (∀ m, m = 4 ∨ m = 5 →
                ¬ Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup m)) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZ'W,hEW,hIW,hD,ρ,hρ,hquot,hAe,hApos,hAupper,
      hdisp,hline,hquad,hker,hEK,hPK⟩ :=
    d.exists_involution_transvection_action h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  let W := Escape.U (T : Subgroup G) L R ⊓
    conjugateSpanBy Z (centralizer ({z} : Set G))
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
  let D := zpowers z
  let := hD
  let := hquot
  have hIZ : I ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  have hWI : W ≤ I := inf_le_left.trans (Escape.U_centralizes_ZS h.layer_centralizes_ZS)
  let hZ : (Z.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer (hWI.trans hIZ)
  let := hZ
  obtain ⟨σ,hσ⟩ := exists_quotient_conjugation_action I W Z hIW hIZ hZ
  let qD := QuotientGroup.mk' (D.subgroupOf W)
  let qZ := QuotientGroup.mk' (Z.subgroupOf W)
  let q : (W ⧸ D.subgroupOf W) →* (W ⧸ Z.subgroupOf W) :=
    QuotientGroup.lift (D.subgroupOf W) qZ (by
      rw [QuotientGroup.ker_mk']; exact subgroupOf_mono W (zpowers_le.mpr hz))
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) y
    exact ⟨qD w,rfl⟩
  have hqe (i : I) (x : W ⧸ D.subgroupOf W) : q (ρ i x) = σ i (q x) := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf W) x
    rw [hρ]
    change qZ _ = σ i (qZ w)
    rw [hσ]
  have hfix (i : I) (x : W ⧸ D.subgroupOf W) (hx : x ∈ q.ker) : ρ i x = x := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf W) x
    change qZ w = 1 at hx
    have hw : (w : G) ∈ Z := (QuotientGroup.eq_one_iff (N := Z.subgroupOf W) w).mp hx
    rw [hρ]
    congr 1
    apply Subtype.ext
    change (i : G) * (w : G) * (i : G)⁻¹ = w
    rw [←mem_centralizer_iff.mp i.property _ hw,mul_inv_cancel_right]
  have hσker := quotient_action_kernel I W Z hIW hIZ hZ σ hσ
  have hDle : D ≤ Z := zpowers_le.mpr hz
  have hID : I ≤ Subgroup.normalizer (D : Set G) :=
    (centralizer_le hDle).trans (Subgroup.centralizer_le_normalizer _)
  have hkerle : ρ.ker ≤ σ.ker := by
    rw [hker,hσker]
    exact subgroupOf_mono I (le_commutatorPreimage (commutatorPreimage_le I W D)
      ((commutator_commutatorPreimage_le I W D hID).trans hDle))
  have hZcard : Nat.card Z' = 4 := by
    rw [card_map_of_injective (MulAut.conj d.representative).injective]
    have hh := (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
    rw [hn] at hh
    exact hh
  have hDle' : D ≤ Z' := by
    have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (D ⊓ Z') Z' bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,hZcard,inf_comm D Z',inf_relIndex_left] at hi
    have hc : D.relIndex Z' = 2 := by
      have hh := hline
      rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hZ'W] at hh
      exact hh
    rw [hc] at hi
    have hmeet : Nat.card (D ⊓ Z' : Subgroup G) = 2 := by
      rw [inf_comm] at hi
      omega
    have he : D ⊓ Z' = D := eq_of_le_of_card_ge inf_le_left (by
      rw [hmeet,Nat.card_zpowers,ho])
    exact he.symm.le.trans inf_le_right
  have hinter : Z ⊓ Z' = D := by
    have hh := (d.parameter_and_intersection h hnat hE hs hNS).2
    exact (eq_of_le_of_card_ge (le_inf hDle hDle') (by
      rw [hh,Nat.card_zpowers,ho])).symm
  have hcomm : ⁅E,W⁆ ≤ Z' := by
    have hh : (⁅W,E⁆.subgroupOf W).map qD ≤ (Z'.subgroupOf W).map qD := by
      rw [←quotient_conjugation_commutatorAction_eq_image I W D E hIW hEI hD ρ hρ]
      exact hdisp.le
    have hkq : qD.ker ≤ Z'.subgroupOf W := by
      rw [QuotientGroup.ker_mk']; exact subgroupOf_mono W hDle'
    have hc : ⁅W,E⁆.subgroupOf W ≤ Z'.subgroupOf W := by
      have hh' := map_le_iff_le_comap.mp hh
      rwa [comap_map_eq_self hkq] at hh'
    have hm := map_mono (f := W.subtype) hc
    rw [map_subgroupOf_eq_of_le (le_normalizer_iff_commutator_le_left.mp (hEI.trans hIW)),
      map_subgroupOf_eq_of_le hZ'W,commutator_comm] at hm
    exact hm
  have hcard := actor_card_of_kernel_lines I W E Z Z' D hIZ hID hinter hcomm
    ρ σ hker hσker hkerle
  let := h.layer_elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (E.subgroupOf I) := IsElementaryAbelian.subgroupOf hEI
  have hquotZ : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W) :=
    IsElementaryAbelian.of_surjective q hq
  have hPI : P ≤ I := conjugateSpanBy_le_self hEI
  have hPN : P ≤ N := hPI.trans hIZ
  let f := ρ.comp (inclusion hPI)
  let g := σ.comp (inclusion hPI)
  have hk : ⁅(⊤ : Subgroup P),f.ker⁆ ≤ pCore 2 P := by
    apply (map_le_map_iff_of_injective P.subtype_injective).mp
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
    apply le_trans (commutator_mono le_rfl ?_) hPK
    rintro _ ⟨x,hx,rfl⟩
    exact mem_map_of_mem I.subtype (show inclusion hPI x ∈ ρ.ker from hx)
  have hcI : (I.pCoreIn 2).subgroupOf I ≤ σ.ker :=
    quotient_conjugation_action_kills_commutator_layer I W Z (I.pCoreIn 2)
      hZ hIW ((commutator_mono inf_le_left le_rfl).trans (natural_escape_core h hnat).2) σ hσ
  have hc : pCore 2 P ≤ g.ker := by
    intro p hp
    exact hcI (pCoreIn_mono_of_normalizes hPI (le_normalizer_conjugateSpanBy E I)
      (mem_map_of_mem P.subtype hp))
  obtain ⟨φ,hφ,hφc,hφe,hred⟩ := NaturalFactorLift.quotient_action_central_cover f g q
    (fun p => hqe (inclusion hPI p)) (fun p => hfix (inclusion hPI p))
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (W ⧸ D.subgroupOf W))) hk hc
  obtain ⟨j,hj,hjn,hje⟩ := NaturalFactorLift.relative_embedding P N hPN
    (NaturalFactorLift.centralizer_span_subnormal Z E hEI)
  refine ⟨hn,z,a,hz,ho,hEI,?_,hPI,hPN,hIW,hZ,σ,hσ,
    hquotZ,IsElementaryAbelian.map σ,
    (by rwa [hcard]),(by rwa [hcard]),φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,?_⟩
  · exact le_inf ((show Z ≤ layer L R from inf_le_left).trans (Escape.layer_le_U _ _ _))
      (le_conjugateSpanBy _ _)
  · exact fun D hD => lifted_component_sieve (hn ▸ h) (hn ▸ hnat) φ hφ hφc j hj hjn D hD

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
