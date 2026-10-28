module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialIntersection
public import Theory.Frattini.PGroupMap
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.SpecificGroups.Triality.ArmsFusionPair
public import Theory.SpecificGroups.Triality.ConcreteBruhat.RootData

/-!
# A centralizing long-root pair for the actual triality special core

The two lower positive long-root groups centralize the highest short-root
involution. Their commutators fill the highest long-root group. Their join
lies in the arms radical, whose Frattini subgroup is that highest root,
so its Frattini subgroup is exactly the highest root. The faithful radical
coordinates and the short-root fixed-space calculation supply an element
of the unipotent group moving the involution modulo the highest root.

Transport through both inverse maps of the compatible parabolic comparison
makes the Weyl conjugations actual ambient conjugations. Agreement on the
whole overlap is essential. Residual and core transport identify the root
center with Z(K), for K = O²(H), and the pair with a subgroup of Q = O₂(K).
The unique normal Sylow subgroup of the model Borel and the original F.1.1
marking identify the unipotent image with S = O₂(N_G(L) ∩ H).

The retained right-factor map marks the chosen short-root involution. TI
then makes the pair centralize every conjugate of Z(K) containing it.
The existing intersection counts contradict the two simultaneous source
placements: their saturation S = Q C_{Q^g}(Z) would fix the involution
modulo Z. The centralizer conjugations supplying these placements, with
coherent transport of the marked involution and mover, remain to be proved.
Original uniqueness in Preparation and the compatible comparison remain
inputs; exhaustive comparison and ambient completion recognition are not
asserted here. The Chapter12 companion applies this to the literal setup.

Source: Aschbacher–Smith F.4.35, printed p.292, and F.1.12(I)(4),
pp.262–264 (`refs/quasithin.pdf`). The coordinate formulas reuse the
existing licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No additional ATLAS source is copied here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityRootPair
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat
open _root_.Triality.Standard.RadicalCoordinates
open _root_.Triality.Standard.RadicalCoordinates.Centers
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.EvenInvolutionGeometry.ArmsNormalization
variable (P : Parameters) (hp : P.prime = 2)

private theorem long_radical (i : Fin 3) (a : fixedField P) :
    long P hp i a ∈ radical P .arms := by
  rw [radical_eq_descendedRootSubgroup P hp .arms]
  exact long_mem P hp .arms i trivial a

private theorem short_radical (a : ExtensionField P) :
    short P hp 2 a ∈ radical P .arms := by
  rw [radical_eq_descendedRootSubgroup P hp .arms]
  exact short_mem P hp .arms 2 (by change (2 : Fin 3) ≠ 0; decide) a

private theorem short_unipotent (a : ExtensionField P) :
    short P hp 0 a ∈ unipotent P :=
  descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .central)
    (short_mem P hp .central 0 trivial a)

private def longHom (i : Fin 3) :
    @MonoidHom (Multiplicative (fixedField P)) (parabolic P .arms)
      (inferInstance : Group (Multiplicative (fixedField P))).toMulOne
      (inferInstance : Group (parabolic P .arms)).toMulOne where
  toFun a := ⟨long P hp i a.toAdd,radical_le_parabolic P .arms (long_radical P hp i _)⟩
  map_one' := Subtype.ext (long_zero P hp i)
  map_mul' a b := by
    apply Subtype.ext
    change long P hp i (a.toAdd+b.toAdd) = long P hp i a.toAdd * long P hp i b.toAdd
    exact long_add P hp i a.toAdd b.toAdd

private theorem long_two_eq (a : fixedField P) :
    long P hp 2 a = highestHom P hp (Multiplicative.ofAdd a) := by
  have he : elementaryInclusion P (longElementary P hp 2 a) =
      elementaryInclusion P (elementaryHighestHom P hp (Multiplicative.ofAdd a)) :=
    (longElementary_val P hp 2 a).trans
      (elementaryHighestHom_val P hp (Multiplicative.ofAdd a)).symm
  exact congrArg (toCarrier P) (elementaryInclusion_injective P he)

private theorem long_center_range :
    ((longHom P hp 2).range).map (parabolic P .arms).subtype = highestRoot P := by
  rw [←MonoidHom.range_comp,←highestHom_range P hp]
  apply congrArg MonoidHom.range
  apply MonoidHom.ext
  intro a
  exact long_two_eq P hp a.toAdd

private def shortPoint (a : ExtensionField P) : parabolic P .arms :=
  ⟨short P hp 2 a,radical_le_parabolic P .arms (short_radical P hp a)⟩

private theorem shortPoint_val (a : ExtensionField P) :
    (shortPoint P hp a).val = short P hp 2 a := rfl

private theorem coordinates_short (a : ExtensionField P) :
    (armsCoordinates P hp (![0,a],![0,0,0])).val = short P hp 2 a := by
  rw [armsCoordinates_factorization]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,long_zero,short_zero,one_mul,mul_one]

private theorem coordinates_long (e f : fixedField P) :
    (armsCoordinates P hp (0,![0,e,f])).val = long P hp 1 e * long P hp 2 f := by
  rw [armsCoordinates_factorization]
  simp only [Pi.zero_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,long_zero,short_zero,one_mul,mul_one]

private theorem short_not_highest (a : ExtensionField P) (ha : a ≠ 0) :
    short P hp 2 a ∉ highestRoot P := by
  rw [←highestHom_range P hp]
  rintro ⟨z,hz⟩
  have hcenter : (armsCoordinates P hp (centralParameters P z.toAdd)).val =
      highestHom P hp z := by
    rw [armsCoordinates_factorization]
    simpa only [centralParameters, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, long_zero, short_zero, one_mul,
      ofAdd_toAdd]
      using long_two_eq P hp z.toAdd
  have hc : armsCoordinates P hp (![0,a],![0,0,0]) =
      armsCoordinates P hp (centralParameters P z.toAdd) := by
    apply Subtype.ext
    exact (coordinates_short P hp a).trans (hz.symm.trans hcenter.symm)
  have he := congrFun (congrArg Prod.fst ((armsCoordinates P hp).injective hc)) 1
  exact ha he

private theorem short_moved (a : ExtensionField P) (ha : a ≠ 0) :
    ∃ x ∈ unipotent P, ⁅x,short P hp 2 a⁆ ∉ highestRoot P := by
  by_contra! h
  obtain ⟨e,f,hef⟩ := fixed_mod_center_long_support P hp
    ⟨short P hp 2 a,short_radical P hp a⟩ (fun b => h _ (short_unipotent P hp b))
  have hc : armsCoordinates P hp (![0,a],![0,0,0]) = armsCoordinates P hp (0,![0,e,f]) := by
    apply Subtype.ext
    exact (coordinates_short P hp a).trans (hef.trans (coordinates_long P hp e f).symm)
  exact ha (congrFun (congrArg Prod.fst ((armsCoordinates P hp).injective hc)) 1)

private theorem short_order (a : ExtensionField P) (ha : a ≠ 0) :
    orderOf (shortPoint P hp a) = 2 := by
  let : CharP (ExtensionField P) 2 := rankOneExtensionCharTwo P hp
  apply orderOf_eq_prime_iff.mpr
  refine ⟨?_,?_⟩
  · apply Subtype.ext
    change short P hp 2 a ^ 2 = 1
    rw [pow_two]
    rw [←short_add,CharTwo.add_self_eq_zero,short_zero]
  · intro he
    exact short_not_highest P hp a ha (by rw [show short P hp 2 a = 1 from congrArg Subtype.val he]; exact one_mem _)

private def armsWeyl : parabolic P .arms :=
  ⟨weylRepresentative P hp (.sr 0),by
    rw [show DihedralGroup.sr 0 = relativeReflection .arms from rfl,weylRepresentative_simple]
    exact simpleRepresentative_mem_parabolic P hp .arms⟩
private def centralWeyl : parabolic P .central :=
  ⟨weylRepresentative P hp (.sr 1),by
    rw [show DihedralGroup.sr 1 = relativeReflection .central from rfl,weylRepresentative_simple]
    exact simpleRepresentative_mem_parabolic P hp .central⟩

private theorem arms_long_zero (a : fixedField P) :
    (armsWeyl P hp).val * long P hp 0 a * (armsWeyl P hp).val⁻¹ = long P hp 1 a := by
  have hh := rotation_long_zero P hp a
  rw [show (DihedralGroup.r 5 : DihedralGroup 6) = .sr 1 * .sr 0 by decide,
    weylRepresentative_mul] at hh
  have hc := central_long_one P hp a
  apply (MulAut.conj (centralWeyl P hp).val).injective
  change (centralWeyl P hp).val * ((armsWeyl P hp).val * long P hp 0 a *
    (armsWeyl P hp).val⁻¹) * (centralWeyl P hp).val⁻¹ =
      (centralWeyl P hp).val * long P hp 1 a * (centralWeyl P hp).val⁻¹
  rw [show (centralWeyl P hp).val * ((armsWeyl P hp).val * long P hp 0 a *
      (armsWeyl P hp).val⁻¹) * (centralWeyl P hp).val⁻¹ =
      ((centralWeyl P hp).val * (armsWeyl P hp).val) * long P hp 0 a *
        ((centralWeyl P hp).val * (armsWeyl P hp).val)⁻¹ by group]
  exact hh.trans hc.symm

private theorem long_one_commute (a : fixedField P) (t : ExtensionField P) :
    Commute (long P hp 1 a) (short P hp 2 t) := by
  have hc (v w : ArmsParameters P) :
      ⁅armsCoordinates P hp v,armsCoordinates P hp w⁆ =
        armsCoordinates P hp (centralParameters P (armsCommutator P v w)) := by
    let f := MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P hp .arms).symm
    exact (map_commutatorElement f.toMonoidHom _ _).symm.trans
      (congrArg f (armsEquiv_commutator P hp v w))
  have hh := congrArg (fun q : radical P .arms => q.val)
    (hc (0,![0,a,0]) (![0,t],![0,0,0]))
  change ⁅(armsCoordinates P hp (0,![0,a,0])).val,
    (armsCoordinates P hp (![0,t],![0,0,0])).val⁆ =
      (armsCoordinates P hp (centralParameters P
        (armsCommutator P (0,![0,a,0]) (![0,t],![0,0,0])))).val at hh
  have hz : armsCommutator P (0,![0,a,0]) (![0,t],![0,0,0]) = 0 := by
    simp [armsCommutator,armsCocycle]
  rw [hz] at hh
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [armsCoordinates_factorization,armsCoordinates_factorization,armsCoordinates_factorization] at hh
  simpa only [centralParameters,Pi.zero_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,long_zero,short_zero,one_mul,mul_one] using hh

private theorem model_pair_frattini {G : Type*} [Group G] [Finite G]
    (f : parabolic P .arms →* G) (hf : Function.Injective f) :
    let U := (f.comp (longHom P hp 0)).range ⊔ (f.comp (longHom P hp 1)).range
    (frattini U).map U.subtype = (f.comp (longHom P hp 2)).range := by
  let U := (f.comp (longHom P hp 0)).range ⊔ (f.comp (longHom P hp 1)).range
  let Q := (radical P .arms).subgroupOf (parabolic P .arms)
  have hroot (i : Fin 3) : (longHom P hp i).range ≤ Q := by
    rintro _ ⟨a,rfl⟩
    exact long_radical P hp i _
  have hUQ : U ≤ Q.map f := by
    apply sup_le <;> rw [MonoidHom.range_comp]
    exact map_mono (hroot 0)
    exact map_mono (hroot 1)
  have hpQ : IsPGroup 2 (Q.map f) := ((radical_isPGroup P hp .arms).comap_subtype).map f
  let : Fact (IsPGroup 2 U) := ⟨hpQ.to_le hUQ⟩
  have hQQ : (frattini Q).map Q.subtype = (longHom P hp 2).range := by
    let eqv : Q ≃* radical P .arms := subgroupOfEquivOfLe (radical_le_parabolic P .arms)
    apply map_injective (parabolic P .arms).subtype_injective
    rw [map_map]
    have he : (parabolic P .arms).subtype.comp Q.subtype =
        (radical P .arms).subtype.comp eqv.toMonoidHom := rfl
    rw [he,←map_map,frattini_map_equiv,←center_radical_arms_eq_frattini P hp,
      embedded_center_radical_arms P hp,long_center_range]
  apply le_antisymm
  · let : Fact (IsPGroup 2 (Q.map f)) := ⟨hpQ⟩
    have hmono := map_mono (f := (Q.map f).subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hUQ))
    let eqv := Q.equivMapOfInjective f hf
    rw [←frattini_map_equiv eqv,map_map,map_map] at hmono
    have hmap : (Q.map f).subtype.comp eqv.toMonoidHom = f.comp Q.subtype := rfl
    rw [hmap] at hmono
    change (frattini U).map U.subtype ≤ (frattini Q).map (f.comp Q.subtype) at hmono
    rw [←map_map,hQQ] at hmono
    simpa only [map_map,MonoidHom.range_comp] using hmono
  · rintro _ ⟨a,rfl⟩
    have hc : ⁅longHom P hp 0 a,longHom P hp 1 (Multiplicative.ofAdd 1)⁆ = longHom P hp 2 a := by
      apply Subtype.ext
      exact (higher_short_root_pair P hp 0 a.toAdd).2.2.2.2.trans (long_two_eq P hp a.toAdd).symm
    rw [show (f.comp (longHom P hp 2)) a =
        ⁅f (longHom P hp 0 a),f (longHom P hp 1 (Multiplicative.ofAdd 1))⁆ by
      rw [←map_commutatorElement,hc]; rfl]
    apply map_mono (commutator_le_frattini_of_isPGroup (p := 2))
    rw [map_subtype_commutator]
    exact commutator_mem_commutator (mem_sup_left ⟨a,rfl⟩) (mem_sup_right ⟨_,rfl⟩)

private theorem pair_transport {G : Type*} [Group G] [Finite G]
    (f : parabolic P .arms →* G) (hf : Function.Injective f)
    (l : parabolic P .central →* G)
    (hagree : ∀ x : Carrier P, ∀ h₁ : x ∈ parabolic P .arms,
      ∀ h₂ : x ∈ parabolic P .central, f ⟨x,h₁⟩ = l ⟨x,h₂⟩)
    (t : ExtensionField P) (ht : t ≠ 0) :
    let Z := (f.comp (longHom P hp 2)).range
    let Q := ((radical P .arms).subgroupOf (parabolic P .arms)).map f
    ∃ v ∈ Q, v = f (shortPoint P hp t) ∧ v ∉ Z ∧ orderOf v = 2 ∧
      (∃ x ∈ ((unipotent P).subgroupOf (parabolic P .arms)).map f, ⁅x,v⁆ ∉ Z) ∧
      ∃ r s : G,
      let U := Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom
      U ≤ Q ∧ U ≤ centralizer ({v} : Set G) ∧ (frattini U).map U.subtype = Z := by
  let s := (l (centralWeyl P hp))⁻¹
  let r := (f (armsWeyl P hp))⁻¹*s
  have hlongC (i : Fin 3) (a : fixedField P) : long P hp i a ∈ parabolic P .central :=
    (unipotent_le_borel P).trans (borel_le_parabolic P .central)
      (descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms)
        (long_mem P hp .arms i trivial a))
  have hconj1 (a : Multiplicative (fixedField P)) :
      s*f (longHom P hp 2 a)*s⁻¹ = f (longHom P hp 1 a) := by
    rw [hagree _ (longHom P hp 2 a).property (hlongC 2 a.toAdd),
      hagree _ (longHom P hp 1 a).property (hlongC 1 a.toAdd)]
    change (l (centralWeyl P hp))⁻¹*l _*((l (centralWeyl P hp))⁻¹)⁻¹ = l _
    rw [←map_inv,←map_inv,←map_mul,←map_mul]
    apply congrArg l
    apply Subtype.ext
    have hc := central_long_one P hp a.toAdd
    change (centralWeyl P hp).val⁻¹*long P hp 2 a.toAdd*
      ((centralWeyl P hp).val⁻¹)⁻¹ = long P hp 1 a.toAdd
    rw [←hc]
    dsimp only [centralWeyl]
    group
  have hconj0 (a : Multiplicative (fixedField P)) :
      r*f (longHom P hp 2 a)*r⁻¹ = f (longHom P hp 0 a) := by
    calc
      _ = (f (armsWeyl P hp))⁻¹ * (s*f (longHom P hp 2 a)*s⁻¹) *
          ((f (armsWeyl P hp))⁻¹)⁻¹ := by dsimp only [r]; group
      _ = (f (armsWeyl P hp))⁻¹ * f (longHom P hp 1 a) *
          ((f (armsWeyl P hp))⁻¹)⁻¹ := by rw [hconj1]
      _ = f ((armsWeyl P hp)⁻¹ * longHom P hp 1 a * ((armsWeyl P hp)⁻¹)⁻¹) := by simp only [map_mul,map_inv]
      _ = f (longHom P hp 0 a) := by
        apply congrArg f
        apply Subtype.ext
        change (armsWeyl P hp).val⁻¹*long P hp 1 a.toAdd*((armsWeyl P hp).val⁻¹)⁻¹ = long P hp 0 a.toAdd
        rw [←arms_long_zero P hp a.toAdd]
        group
  have hmap (g : G) (i : Fin 3)
      (hg : ∀ a, g*f (longHom P hp 2 a)*g⁻¹ = f (longHom P hp i a)) :
      ((f.comp (longHom P hp 2)).range).map (MulAut.conj g).toMonoidHom =
        (f.comp (longHom P hp i)).range := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨a,(hg a).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨_,⟨a,rfl⟩,hg a⟩
  refine ⟨f (shortPoint P hp t),mem_map_of_mem _ (short_radical P hp t),rfl,?_,?_,?_,r,s,?_⟩
  · rintro ⟨a,ha⟩
    have he := congrArg Subtype.val (hf ha)
    change long P hp 2 a.toAdd = short P hp 2 t at he
    exact short_not_highest P hp t ht (he ▸ (show long P hp 2 a.toAdd ∈ highestRoot P from
      (highestHom_range P hp) ▸ ⟨a,(long_two_eq P hp a.toAdd).symm⟩))
  · exact (orderOf_injective f hf _).trans (short_order P hp t ht)
  · obtain ⟨x,hx,hxv⟩ := short_moved P hp t ht
    let y : parabolic P .arms := ⟨x,(unipotent_le_borel P).trans (borel_le_parabolic P .arms) hx⟩
    refine ⟨f y,mem_map_of_mem _ hx,?_⟩
    rintro ⟨a,ha⟩
    have he : f (longHom P hp 2 a) = f ⁅y,shortPoint P hp t⁆ := by
      simpa only [map_commutatorElement,MonoidHom.comp_apply] using ha
    have hh := congrArg Subtype.val (hf he)
    change long P hp 2 a.toAdd = ⁅x,short P hp 2 t⁆ at hh
    exact hxv (hh ▸ (show long P hp 2 a.toAdd ∈ highestRoot P from
      (highestHom_range P hp) ▸ ⟨a,(long_two_eq P hp a.toAdd).symm⟩))
  · dsimp only
    rw [hmap r 0 hconj0,hmap s 1 hconj1]
    refine ⟨sup_le ?_ ?_,sup_le ?_ ?_,model_pair_frattini P hp f hf⟩
    · rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem f (long_radical P hp 0 _)
    · rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem f (long_radical P hp 1 _)
    · rintro _ ⟨a,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have hc : Commute (longHom P hp 0 a) (shortPoint P hp t) := by
        apply Subtype.ext
        exact (higher_short_root_pair P hp t a.toAdd).2.2.1.eq
      exact (hc.map f).eq
    · rintro _ ⟨a,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have hc : Commute (longHom P hp 1 a) (shortPoint P hp t) := by
        apply Subtype.ext
        exact (long_one_commute P hp a.toAdd t).eq
      exact (hc.map f).eq

include hp in
private theorem local_center :
    (center (localFactor P .arms)).map (localFactor P .arms).subtype = highestRoot P := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    have hc : a.val ∈ centralizer (radical P .arms : Set (Carrier P)) := by
      apply mem_centralizer_iff.mpr
      intro r hr
      exact congrArg Subtype.val
        (mem_center_iff.mp ha ⟨r,radical_le_localFactor P hp .arms hr⟩)
    have har := parabolic_centralizer_radical_le P hp .arms
      ⟨localFactor_le_parabolic P .arms a.property,hc⟩
    rw [←embedded_center_radical_arms P hp]
    refine ⟨⟨a.val,har⟩,mem_center_iff.mpr (fun r => ?_),rfl⟩
    apply Subtype.ext
    exact congrArg (fun x : localFactor P .arms => x.val)
      (mem_center_iff.mp ha ⟨r,radical_le_localFactor P hp .arms r.property⟩)
  · intro z hz
    have hzR : z ∈ radical P .arms := by
      rw [←embedded_center_radical_arms P hp] at hz
      exact map_subtype_le _ hz
    refine ⟨⟨z,radical_le_localFactor P hp .arms hzR⟩,mem_center_iff.mpr (fun x => ?_),rfl⟩
    apply Subtype.ext
    have hh := localFactor_arms_le_centralizer_center_unipotent P hp x.property
    rw [embedded_center_unipotent P hp] at hh
    exact (mem_centralizer_iff.mp hh z hz).symm

private theorem core_commutator {G : Type*} [Group G]
    (f : parabolic P .arms →* G) :
    let Q := ((radical P .arms).subgroupOf (parabolic P .arms)).map f
    ⁅Q,Q⁆ ≤ (f.comp (longHom P hp 2)).range := by
  dsimp only
  rw [←map_commutator,MonoidHom.range_comp]
  apply map_mono
  apply (map_le_map_iff_of_injective (parabolic P .arms).subtype_injective).mp
  rw [map_commutator,map_subgroupOf_eq_of_le (radical_le_parabolic P .arms),
    ←map_subtype_commutator,←center_radical_arms_eq_commutator P hp,
    embedded_center_radical_arms P hp,long_center_range P hp]


private theorem saturation_fixes_point_mod_center
    {G : Type*} [Group G] {K S : Subgroup G} {v : G}
    (hv : v ∈ K.pCoreIn 2) (hc : ⁅K.pCoreIn 2,K.pCoreIn 2⁆ ≤ (center K).map K.subtype)
    (hn : S ≤ normalizer (K.pCoreIn 2 : Set G))
    (g : G) (hvg : v ∈ ((center K).map K.subtype).map (MulAut.conj g).toMonoidHom)
    (hS : S = K.pCoreIn 2 ⊔ ((K.pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center K).map K.subtype : Subgroup G) : Set G))) :
    ∀ x ∈ S, ⁅x,v⁆ ∈ (center K).map K.subtype := by
  let Q := K.pCoreIn 2
  let R := Q.map (MulAut.conj g).toMonoidHom ⊓
    centralizer (((center K).map K.subtype : Subgroup G) : Set G)
  have hRN : R ≤ normalizer (Q : Set G) := (le_sup_right.trans hS.ge).trans hn
  have hRV : R ≤ centralizer ({v} : Set G) := by
    rintro x ⟨⟨y,hy,rfl⟩,_⟩
    obtain ⟨z,⟨k,hk,rfl⟩,he⟩ := hvg
    apply mem_centralizer_singleton_iff.mpr
    rw [←he,←map_mul,←map_mul]
    exact congrArg (MulAut.conj g).toMonoidHom (congrArg (fun t : K => t.val)
      (mem_center_iff.mp hk ⟨y,map_subtype_le _ hy⟩))
  intro x hx
  have hx' : x ∈ (Q : Set G) * (R : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q R hRN]
    exact hS ▸ hx
  obtain ⟨q,hq,r,hr,rfl⟩ := hx'
  have he : ⁅r,v⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_singleton_iff.mp (hRV hr))
  rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,mul_inv_cancel,one_mul]
  exact hc (commutator_mem_commutator hq hv)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.TrialityRootPair

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat
open _root_.Triality.Standard.RadicalCoordinates
open _root_.Triality.Standard.RadicalCoordinates.Centers
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
variable {G : Type*} [Group G] [Finite G]

private theorem triality_comparison_images
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (P : Parameters) (hP : P.prime = 2)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam P).reverse) :
    let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
    (f.comp (TrialityRootPair.longHom P hP 2)).range =
      (center (residual H)).map (residual H).subtype ∧
    ((radical P .arms).subgroupOf (parabolic P .arms)).map f = (residual H).pCoreIn 2 := by
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Y₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  let J := (localFactor P .arms).subgroupOf (parabolic P .arms)
  have hJ : J = solvableResidual (parabolic P .arms) := by
    apply map_injective (parabolic P .arms).subtype_injective
    rw [map_subgroupOf_eq_of_le (localFactor_le_parabolic P .arms),
      TrialityComparison.arms_parabolic_residual P hP]
  have hJf : J.map f = residual H := by
    rw [hJ,show f = Y.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hTH hp 1
  have hCJ : (center J).map J.subtype = (TrialityRootPair.longHom P hP 2).range := by
    apply map_injective (parabolic P .arms).subtype_injective
    rw [map_subgroup_center_eq _ (parabolic P .arms).subtype_injective,
      map_subgroupOf_eq_of_le (localFactor_le_parabolic P .arms),TrialityRootPair.local_center P hP,
      TrialityRootPair.long_center_range P hP]
  have hZ : (f.comp (TrialityRootPair.longHom P hP 2)).range =
      (center (residual H)).map (residual H).subtype := by
    rw [MonoidHom.range_comp,←hCJ,map_subgroup_center_eq f hf,hJf]
  have hQ : ((radical P .arms).subgroupOf (parabolic P .arms)).map f = (residual H).pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 (localFactor P .arms) (parabolic P .arms)
      (localFactor_le_parabolic P .arms),show (localFactor P .arms).pCoreIn 2 = radical P .arms from
        localFactor_twoCore_map P hP .arms] at hh
    exact hh
  exact ⟨hZ,hQ⟩

private theorem triality_borel_pSubgroup
    (P : Parameters) (hP : P.prime = 2) (V : Subgroup (Carrier P))
    (hVP : IsPGroup 2 V) (hVB : V ≤ borel P) : V ≤ unipotent P := by
  have hUB : (unipotentSylow P hP : Subgroup (Carrier P)) ≤ borel P := by
    rw [coe_unipotentSylow]
    exact unipotent_le_borel P
  let U := (unipotentSylow P hP).subtype hUB
  have hU : (U : Subgroup (borel P)) = (unipotent P).subgroupOf (borel P) := by
    dsimp only [U]
    rw [Sylow.coe_subtype,coe_unipotentSylow]
  let : (U : Subgroup (borel P)).Normal := by
    rw [hU]
    exact normal_subgroupOf_of_le_normalizer (normalizer_unipotent_eq_borel P hP).ge
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  obtain ⟨D,hD⟩ := (hVP.comap_subtype : IsPGroup 2 (V.subgroupOf (borel P))).exists_le_sylow
  have hDU : D = U := Subsingleton.elim _ _
  show V ≤ unipotent P
  intro x hx
  have hh := hD (show (⟨x,hVB hx⟩ : borel P) ∈ V.subgroupOf (borel P) from hx)
  rw [hDU] at hh
  change (⟨x,hVB hx⟩ : borel P) ∈ (U : Subgroup (borel P)) at hh
  rw [hU] at hh
  exact hh

omit [Finite G] in
private theorem amalgam_right_value
    {M : Type*} [Group M] (X₀ X₁ : Subgroup G) (Y₀ Y₁ B : Subgroup M)
    (h₀ : B ≤ Y₀) (h₁ : B ≤ Y₁)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups X₀ (X₀ ⊓ X₁) X₁ inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups Y₀ B Y₁ h₀ h₁)) (b : (X₀ ⊓ X₁ : Subgroup G)) :
    (e.right ⟨b.val,b.property.2⟩).val = (e.middle b).val :=
  congrArg (fun y : Y₁ => y.val) (e.right_commutes b)

omit [Finite G] in
private theorem amalgam_inverse_value
    {M : Type*} [Group M] (X₀ X₁ : Subgroup G) (Y₀ Y₁ B : Subgroup M)
    (h₀ : B ≤ Y₀) (h₁ : B ≤ Y₁)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups X₀ (X₀ ⊓ X₁) X₁ inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups Y₀ B Y₁ h₀ h₁)) (b : B) :
    (e.right.symm ⟨b.val,h₁ b.property⟩).val =
      (e.left.symm ⟨b.val,h₀ b.property⟩).val :=
  (congrArg (fun y : X₁ => y.val) (e.symm.right_commutes b)).trans
    (congrArg (fun y : X₀ => y.val) (e.symm.left_commutes b)).symm

omit [Finite G] in
private theorem triality_source_borel_image
    {L H : Subgroup G} (P : Parameters)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam P).reverse) :
    let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    let a : Y →* Carrier P := (parabolic P .arms).subtype.comp e.right.toMonoidHom
    ((sourceS L H).subgroupOf Y).map a ≤ borel P := by
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Y₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let a : Y →* Carrier P := (parabolic P .arms).subtype.comp e.right.toMonoidHom
  change ((sourceS L H).subgroupOf Y).map a ≤ borel P
  rintro _ ⟨x,hx,rfl⟩
  let b : (Y₀ ⊓ Y : Subgroup G) := ⟨x.val,((show sourceS L H ≤ Y₀ from le_sup_right.trans le_sup_left) hx),x.property⟩
  have heq := amalgam_right_value Y₀ Y (parabolic P .central) (parabolic P .arms)
    (borel P) (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e b
  change a x = (e.middle b).val at heq
  rw [heq]
  exact (e.middle b).property

private theorem triality_unipotent_image
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (P : Parameters) (hP : P.prime = 2)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam P).reverse) :
    let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
    ((unipotent P).subgroupOf (parabolic P .arms)).map f = sourceS L H := by
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Y₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  let a : Y →* Carrier P := (parabolic P .arms).subtype.comp e.right.toMonoidHom
  let V := ((sourceS L H).subgroupOf Y).map a
  have hVP : IsPGroup 2 V := ((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map a
  have hVB : V ≤ borel P := triality_source_borel_image P e
  have hVU := triality_borel_pSubgroup P hP V hVP hVB
  obtain ⟨D,hD⟩ := (d.hypothesisF11 h hTH).sylow_parabolic 1
  let U' := ((unipotent P).subgroupOf (parabolic P .arms)).map e.right.symm.toMonoidHom
  have hSU : (D : Subgroup Y) ≤ U' := by
    intro x hx
    have hxS : x.val ∈ sourceS L H := hD.le (mem_map_of_mem Y.subtype hx)
    have hxU : a x ∈ unipotent P := hVU (mem_map_of_mem a hxS)
    exact ⟨e.right x,hxU,e.right.symm_apply_apply x⟩
  have heq := D.is_maximal' (((unipotent_isPGroup_binary P hP).comap_subtype).map e.right.symm.toMonoidHom) hSU
  change ((unipotent P).subgroupOf (parabolic P .arms)).map (Y.subtype.comp e.right.symm.toMonoidHom) = _
  rw [←map_map]
  change U'.map Y.subtype = _
  change U' = (D : Subgroup Y) at heq
  rw [heq]
  exact hD

omit [Finite G] in
private theorem triality_inverse_overlap
    {L H : Subgroup G} (P : Parameters) (hP : P.prime = 2)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam P).reverse)
    (x : Carrier P) (hx : x ∈ parabolic P .arms) (hy : x ∈ parabolic P .central) :
    (e.right.symm ⟨x,hx⟩).val = (e.left.symm ⟨x,hy⟩).val := by
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Y₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let b : borel P := ⟨x,(parabolic_inf_binary P hP).le ⟨hx,hy⟩⟩
  exact amalgam_inverse_value Y₀ Y (parabolic P .central) (parabolic P .arms)
    (borel P) (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e b

private theorem prepared_triality_pair
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (P : Parameters) (hP : P.prime = 2)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam P).reverse) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ v ∈ Q,
      (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val = v ∧ (e.right w).val = short P hP 2 1) ∧
      v ∉ Z ∧ orderOf v = 2 ∧
      (∃ x ∈ sourceS L H, ⁅x,v⁆ ∉ Z) ∧ ∃ r s : G,
      let U := Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom
      U ≤ Q ∧ U ≤ centralizer ({v} : Set G) ∧ (frattini U).map U.subtype = Z ∧
      ⁅Q,Q⁆ ≤ Z := by
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Y₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic P .central →* G := Y₀.subtype.comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  have ha (x : Carrier P) (hx : x ∈ parabolic P .arms) (hy : x ∈ parabolic P .central) :
      f ⟨x,hx⟩ = l ⟨x,hy⟩ := triality_inverse_overlap P hP e x hx hy
  obtain ⟨hZ,hQ⟩ := triality_comparison_images d h hTH hp P hP e
  have hS := triality_unipotent_image d h hTH P hP e
  have hh := TrialityRootPair.pair_transport P hP f hf l ha 1 one_ne_zero
  dsimp only at hh ⊢
  rw [hZ,hQ,hS] at hh
  obtain ⟨v,hv,hvmark,hvz,hv2,hmoved,r,s,hUQ,hUC,hfrat⟩ := hh
  refine ⟨v,hv,?_,hvz,hv2,hmoved,r,s,hUQ,hUC,hfrat,?_⟩
  · refine ⟨e.right.symm (TrialityRootPair.shortPoint P hP 1),hvmark.symm,?_⟩
    exact (congrArg (fun y : parabolic P .arms => y.val)
      (e.right.apply_symm_apply (TrialityRootPair.shortPoint P hP 1))).trans
        (TrialityRootPair.shortPoint_val P hP 1)
  · have hc := TrialityRootPair.core_commutator P hP f
    dsimp only at hc
    rwa [hQ,hZ] at hc

/-- The actual triality arms core contains a marked highest short-root
involution with a centralizing pair of conjugate long-root groups. Their
join has Frattini subgroup exactly Z(K). The same involution is moved
modulo Z(K) by an element of the original intersection core S. -/
theorem Preparation.triality_special_core_root_pair
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse,
      ∃ v ∈ Q,
      (∃ w : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        w.val = v ∧ (e.right w).val = short (binaryParameters m hm) rfl 2 1) ∧
      v ∉ Z ∧ orderOf v = 2 ∧
      (∃ x ∈ sourceS L H, ⁅x,v⁆ ∉ Z) ∧ ∃ r s : G,
      let U := Z.map (MulAut.conj r).toMonoidHom ⊔ Z.map (MulAut.conj s).toMonoidHom
      U ≤ Q ∧ U ≤ centralizer ({v} : Set G) ∧ (frattini U).map U.subtype = Z ∧
      (∀ g : G, v ∈ Z.map (MulAut.conj g).toMonoidHom →
        U ≤ centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G)) ∧
      (∀ g : G, v ∈ Z.map (MulAut.conj g).toMonoidHom →
        Z ≤ Q.map (MulAut.conj g).toMonoidHom →
        ¬ Q.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Z : Set G) ≤ sourceS L H) := by
  have hcompare := he
  have hTI := d.triality_right_center_fusion h hH hp m hm he
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hH.1.1.2 hp (binaryParameters m hm) rfl he).elim
  obtain ⟨e⟩ := he
  obtain ⟨v,hv,hmark,hvz,hv2,hmoved,r,s,hUQ,hUC,hfrat,hclass⟩ :=
    prepared_triality_pair d h hH.1.1.2 hp (binaryParameters m hm) rfl e
  refine ⟨e,v,hv,hmark,hvz,hv2,hmoved,r,s,hUQ,hUC,hfrat,?_,?_⟩
  · intro g hvg
    let := hTI.1
    have hv1 : v ≠ 1 := by intro heq; simp [heq] at hv2
    exact center_conjugate_pair hTI.2.1 g r s v hvg hv1
      (le_sup_left.trans hUC) (le_sup_right.trans hUC)
  · intro g hvg hZQ hRS
    have hg : g ∉ normalizer (residual H : Set G) := by
      intro hg
      have hh := mem_normalizer_iff_map_conj_eq.mp (hTI.2.2.symm ▸ hg)
      exact hvz (hh ▸ hvg)
    have hs := (d.triality_special_core_saturation h hH hp m hm hcompare g hg hZQ hRS).2
    have hnQ : sourceS L H ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
      d.S_normalizes_right.trans (normalizer_le_normalizer_characteristic_image
        (residual H) (pCore 2 (residual H)))
    obtain ⟨x,hx,hxv⟩ := hmoved
    exact hxv (TrialityRootPair.saturation_fixes_point_mod_center hv hclass hnQ g hvg hs x hx)

/-- The actual right-factor marking identifies the model unipotent group
with the original intersection core S. This retains the whole overlap map. -/
theorem Preparation.triality_right_unipotent_image
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (P : Parameters) (hP : P.prime = 2)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam P).reverse) :
    let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
    ((unipotent P).subgroupOf (parabolic P .arms)).map f = sourceS L H :=
  triality_unipotent_image d h hTH P hP e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
