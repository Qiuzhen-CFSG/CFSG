module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Models
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Transport
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Full Sylow fixers for triality and large Ree groups

An automorphism fixing the positive Sylow subgroup pointwise commutes with
conjugation by every element of that subgroup. The actual Bruhat geometry
provides a correction from the positive subgroup that aligns the signed root
frame (triality) or opposite unipotent pair (Ree). A power of two kills this
correction, while retaining the alignment and pointwise fixation.

The signed root formulas then force that power to be identity: evaluation at
one removes the scalars, the positive parameters detect the field map, and the
inverse-scalar formulas fix the negative roots. Generation finishes the proof.
This treats arbitrary mixed inner–coefficient automorphisms and excludes odd
coefficient actors as well. It does not infer separate fixation by their factors.
The cubic triality coefficient field is retained even at f = 1; the Ree range
is every m ≥ 1, with the Tits endpoint handled separately by `SmallRank`.

The final applications use the literal component central quotient and the
existing perfect-central-cover reduction. No independent model simplicity or
perfectness certification is needed: Ree inherits these from the source group.

Sources: Aschbacher–Smith, B.1.13, printed pp.73–74 of `refs/quasithin.pdf`;
GLS3 §§2.3–2.5, particularly 2.3.5, Table 2.4, and 2.5.1(b,c),
`refs/KGroup/GLS3/chapter2.tex`. The imported root-coordinate proofs retain
their original source attribution.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers

open Subgroup
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.OuterOdd.Coverage
open Triality.Standard.OuterOdd.Coverage.ParameterRigidity

private theorem rootFrame_pow (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) (ha : PreservesRootFrame P hp a) (k : ℕ) :
    PreservesRootFrame P hp (a ^ k) := by
  induction k with
  | zero => intro s i; simp
  | succ k ih =>
    intro s i
    rw [pow_succ]
    change ((a ^ k) ∘ a) '' Set.range (rootElement P hp s i) = _
    rw [Set.image_comp]
    rw [ha, ih]

private theorem eq_one_of_frame (f : ℕ) (hf : 0 < f) (a : MulAut (BinaryCarrier f hf))
    (ha : PreservesRootFrame (binaryParameters f hf) rfl a)
    (hu : ∀ x ∈ unipotent (binaryParameters f hf), a x = x) : a = 1 := by
  let P := binaryParameters f hf
  apply RootGeometry.ext_of_signed_roots f hf
  intro s i t
  change a (rootElement P rfl s i t) = rootElement P rfl s i t
  obtain ⟨c, e, hpos, hneg⟩ := ParameterRigidity.exists_node_parameters P rfl a ha i
  have he (r : RootField P i) : c.val * e r = r :=
    rootElement_injective P rfl true i ((hpos r).symm.trans
      (hu _ (positive_mem_unipotent P rfl i r)))
  have hc : c.val = 1 := by simpa only [map_one, mul_one] using he 1
  have he' (r : RootField P i) : e r = r := by simpa only [hc, one_mul] using he r
  cases s
  · simpa only [hc, inv_one, one_mul, he'] using hneg t
  · exact hu _ (positive_mem_unipotent P rfl i t)

namespace FixerReduction
variable {G : Type*} [Group G]

private theorem map_eq_of_fixes (U : Subgroup G) (a : MulAut G)
    (ha : ∀ x ∈ U, a x = x) : U.map a.toMonoidHom = U := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change a x ∈ U
    rw [ha x hx]
    exact hx
  · intro x hx
    exact ⟨x, hx, ha x hx⟩

private theorem pow_fixes (U : Subgroup G) (a : MulAut G)
    (ha : ∀ x ∈ U, a x = x) (n : ℕ) : ∀ x ∈ U, (a ^ n) x = x := by
  have ha' : a ∈ fixingSubgroup (MulAut G) (U : Set G) :=
    (mem_fixingSubgroup_iff _).mpr ha
  exact (mem_fixingSubgroup_iff _).mp ((fixingSubgroup _ _).pow_mem ha' n)

private theorem power_of_alignment (U : Subgroup G) (hU : IsPGroup 2 U)
    (R : MulAut G → Prop)
    (hpow : ∀ a, R a → ∀ n : ℕ, R (a ^ n))
    (hrigid : ∀ a, R a → (∀ x ∈ U, a x = x) → a = 1)
    (halign : ∀ a : MulAut G, (∀ x ∈ U, a x = x) →
      ∃ u ∈ U, R (MulAut.conj u * a))
    (a : MulAut G) (ha : ∀ x ∈ U, a x = x) : ∃ k : ℕ, a ^ (2 ^ k) = 1 := by
  obtain ⟨u, hu, hb⟩ := halign a ha
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have huk : u ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hc : Commute (MulAut.conj u) a := by
    apply MulEquiv.ext
    intro x
    change u * a x * u⁻¹ = a (u * x * u⁻¹)
    rw [map_mul, map_mul, map_inv, ha u hu]
  have he : (MulAut.conj u * a) ^ (2 ^ k) = a ^ (2 ^ k) := by
    rw [hc.mul_pow, ← map_pow, huk, map_one, one_mul]
  exact ⟨k, hrigid _ (he ▸ hpow _ hb (2 ^ k)) (pow_fixes U a ha _)⟩

private theorem all_sylows [Finite G] (P : Sylow 2 G)
    (hP : ∀ a : MulAut G, (∀ x ∈ P, a x = x) → ∃ k : ℕ, a ^ (2 ^ k) = 1) :
    SylowFixerIsTwoGroup G := by
  intro S a
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  let e := MulAut.conj g
  have hm : (P : Subgroup G).map e.toMonoidHom = S :=
    congrArg Sylow.toSubgroup hg
  have ha := (mem_fixingSubgroup_iff _).mp a.property
  change ∀ x ∈ S, a.val x = x at ha
  let b := e⁻¹ * a.val * e
  have hb : ∀ x ∈ P, b x = x := by
    intro x hx
    change e.symm (a.val (e x)) = x
    have hxS : e x ∈ (S : Subgroup G) := by
      rw [← hm]
      exact mem_map_of_mem e.toMonoidHom hx
    rw [ha (e x) hxS, e.symm_apply_apply]
  obtain ⟨k, hk⟩ := hP b hb
  have he : MulAut.conj e b = a.val := by
    change e * (e⁻¹ * a.val * e) * e⁻¹ = a.val
    group
  refine ⟨k, Subtype.ext ?_⟩
  change a.val ^ (2 ^ k) = 1
  have h := congrArg (MulAut.conj e) hk
  simpa only [map_pow, he, map_one] using h
end FixerReduction

/-- Every binary triality carrier has a two-group pointwise Sylow fixer, including f = 1. -/
theorem triality_fixer (f : ℕ) (hf : 0 < f) : SylowFixerIsTwoGroup (BinaryCarrier f hf) := by
  apply FixerReduction.all_sylows (unipotentSylow (binaryParameters f hf) rfl)
  exact FixerReduction.power_of_alignment _ (unipotent_isPGroup_binary _ rfl)
    (PreservesRootFrame _ rfl) (rootFrame_pow _ rfl) (eq_one_of_frame f hf)
    (fun a ha => RootGeometry.exists_unipotent_rootFrame f hf a
      (FixerReduction.map_eq_of_fixes _ a ha))

open Subgroup
open ReeF4 ReeF4.LocalBlockInput ReeF4.LargeLocalSeeds
open ReeF4.LocalBlockInput.PairRigidity
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

private theorem map_aut_mul {G : Type*} [Group G] (U : Subgroup G) (a b : MulAut G) :
    U.map (a * b).toMonoidHom = (U.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_conj_mul {G : Type*} [Group G] (U : Subgroup G) (g h : G) :
    U.map (MulAut.conj (g * h)).toMonoidHom =
      (U.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_mul, map_aut_mul]

private theorem map_aut_pow {G : Type*} [Group G] (U : Subgroup G) (a : MulAut G)
    (ha : U.map a.toMonoidHom = U) (n : ℕ) : U.map (a ^ n).toMonoidHom = U := by
  induction n with
  | zero => exact Subgroup.map_id U
  | succ n ih => rw [pow_succ, map_aut_mul, ha, ih]

private theorem ree_pair_pow {m : ℕ} (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (ha : PreservesUnipotentPair d a) (n : ℕ) : PreservesUnipotentPair d (a ^ n) :=
  ⟨map_aut_pow _ a ha.1 n, map_aut_pow _ a ha.2 n⟩

private theorem ree_pair_rigid {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (a : MulAut d.fixedGroup) (hp : PreservesUnipotentPair d a)
    (hfix : ∀ x ∈ standardUnipotent d, a x = x) : a = 1 := by
  have hi := FixedBruhat.standardUnipotent_index_odd d
  have hb := preservesSimpleBlocks_of_preservesUnipotentPair hm d hi a hp
  let C := suzukiCoordinates d
  obtain ⟨c, hc⟩ := exists_parameterRelations hm d hi a hp hb C
  obtain ⟨b, σ, hlin, hsu⟩ := exists_field_on_coordinates_of_relations d a hb C c hc
  have he (t : CoefficientField m) : (b : CoefficientField m) * σ t = t := by
    apply linearElement_injective d true
    exact (hlin true t).symm.trans
      (hfix _ (simpleBlock_positive_le d .linear (linearElement_mem d true t)))
  have hb1 : (b : CoefficientField m) = 1 := by
    simpa only [map_one, mul_one] using he 1
  have hσ (t : CoefficientField m) : σ t = t := by
    simpa only [hb1, one_mul] using he t
  have hc1 : (c : CoefficientField m) = 1 := by
    have h := (hsu true 1 0).symm.trans
      (hfix _ (simpleBlock_positive_le d .suzuki (C.element_mem true 1 0)))
    have hh : ((c : CoefficientField m) * σ 1,
        (centralScale c : CoefficientField m) * σ 0) = (1, 0) := by
      apply C.suzuki_injective true
      exact congrArg (fun x : d.fixedGroup => x.val) h
    have hh' := congrArg Prod.fst hh
    simpa only [signedScale, ↓reduceIte, map_one, mul_one] using hh'
  have hcunit : c = 1 := Units.ext hc1
  have hcc : centralScale c = 1 := by simp [centralScale, hcunit]
  have hbunit : b = 1 := Units.ext hb1
  have hbs (s : Bool) : signedScale b s = 1 := by simp only [signedScale, hbunit, inv_one, ite_self]
  have hcs (s : Bool) : signedScale c s = 1 := by simp only [signedScale, hcunit, inv_one, ite_self]
  have hccs (s : Bool) : signedScale (centralScale c) s = 1 := by simp only [hcc, signedScale, inv_one, ite_self]
  have hlin' (s : Bool) (t : CoefficientField m) :
      a (linearElement d s t) = linearElement d s t := by
    rw [hlin, hbs, Units.val_one, one_mul, hσ]
  have hsu' (s : Bool) (t u : CoefficientField m) :
      a (C.element s t u) = C.element s t u := by
    rw [hsu, hcs, hccs, Units.val_one, one_mul, one_mul, hσ, hσ]
  have heq : a.toMonoidHom = (1 : MulAut d.fixedGroup).toMonoidHom := by
    apply hom_ext_of_simpleBlocks_generate d (simpleBlocks_generate hm d)
    intro s positive x hx
    change a x = x
    cases s with
    | linear =>
      obtain ⟨t, rfl⟩ := linearElement_surjective d positive hx
      exact hlin' positive t
    | suzuki =>
      obtain ⟨t, u, rfl⟩ := C.element_cover positive hx
      exact hsu' positive t u
  exact MulEquiv.ext fun x => DFunLike.congr_fun heq x

private theorem unipotent_alignment {G : Type*} [Group G]
    (U V : Subgroup G) (hdUV : Disjoint U V) (w : G)
    (hw : U.map (MulAut.conj w).toMonoidHom = V)
    (hbruhat : ∀ x : G, ∃ u ∈ U, ∃ n : G,
      (Disjoint U (U.map (MulAut.conj n).toMonoidHom) →
        U.map (MulAut.conj n).toMonoidHom = V) ∧
      ∃ v ∈ U, x = u * n * v)
    (a : MulAut G) (ha : U.map a.toMonoidHom = U) :
    ∃ u ∈ U, U.map (MulAut.conj u * a).toMonoidHom = U ∧
      V.map (MulAut.conj u * a).toMonoidHom = V := by
  have hV : V.map a.toMonoidHom = U.map (MulAut.conj (a w)).toMonoidHom := by
    rw [← hw, Subgroup.map_map]
    have he : a.toMonoidHom.comp (MulAut.conj w).toMonoidHom =
        (MulAut.conj (a w)).toMonoidHom.comp a.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv]
    rw [he, ← Subgroup.map_map, ha]
  have hd : Disjoint U (U.map (MulAut.conj (a w)).toMonoidHom) := by
    rw [← hV, ← ha]
    exact Subgroup.disjoint_map a.injective hdUV
  obtain ⟨u, hu, n, nt, v, hv, he⟩ := hbruhat (a w)
  have huN : U.map (MulAut.conj u).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (U.le_normalizer hu)
  have hvN : U.map (MulAut.conj v).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (U.le_normalizer hv)
  have hcell : U.map (MulAut.conj (a w)).toMonoidHom =
      (U.map (MulAut.conj n).toMonoidHom).map (MulAut.conj u).toMonoidHom := by
    rw [he, map_conj_mul, map_conj_mul, hvN]
  have hdn : Disjoint U (U.map (MulAut.conj n).toMonoidHom) := by
    have hd' : Disjoint (U.map (MulAut.conj u).toMonoidHom)
        ((U.map (MulAut.conj n).toMonoidHom).map (MulAut.conj u).toMonoidHom) := by
      rw [huN, ← hcell]
      exact hd
    apply disjoint_iff.mpr
    apply Subgroup.map_injective (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective
    rw [Subgroup.map_inf _ _ _ (MulAut.conj u).injective, Subgroup.map_bot]
    exact disjoint_iff.mp hd'
  have hn := nt hdn
  have huInv : U.map (MulAut.conj u⁻¹).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (U.le_normalizer (U.inv_mem hu))
  refine ⟨u⁻¹, U.inv_mem hu, ?_, ?_⟩
  · rw [map_aut_mul, ha]
    exact huInv
  · rw [map_aut_mul, hV, hcell, hn, ← map_conj_mul,
      inv_mul_cancel, map_one]
    exact Subgroup.map_id V

private theorem ree_align {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (a : MulAut d.fixedGroup)
    (ha : (standardUnipotent d).map a.toMonoidHom = standardUnipotent d) :
    ∃ u ∈ standardUnipotent d, PreservesUnipotentPair d (MulAut.conj u * a) := by
  obtain ⟨w, hw⟩ := PairNormalization.exists_opposition d
  apply unipotent_alignment (standardUnipotent d) (oppositeUnipotent d)
    (PairNormalization.standardUnipotent_disjoint_opposite d) w hw ?_ a ha
  intro x
  obtain ⟨u, hu, n, ⟨nt⟩, v, hv, he⟩ :=
    PairNormalization.OppositionCell.FixedBruhatCover.exists_root_bruhat hm d x
  exact ⟨u, hu, n, nt.map_standardUnipotent_eq_opposite_of_disjoint d n, v, hv, he⟩

/-- The full fixer bound on the actual supplied large Ree fixed group. Simplicity and
perfectness are inherited from the source consumer. -/
theorem ree_fixed_fixer {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup] :
    SylowFixerIsTwoGroup d.fixedGroup := by
  let S := (standardUnipotent_isPGroup d).toSylow
    (FixedBruhat.standardUnipotent_index_odd d).not_two_dvd_nat
  apply FixerReduction.all_sylows S
  exact FixerReduction.power_of_alignment _ (standardUnipotent_isPGroup d)
    (PreservesUnipotentPair d) (ree_pair_pow d) (ree_pair_rigid hm d)
    (fun a ha => ree_align hm d a (FixerReduction.map_eq_of_fixes _ a ha))

/-- Transport the full fixer bound through the genuine standard triality model witness. -/
theorem triality_model_fixer {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hf : 0 < f) (hmodel : IsTrialityGroupAt (2 ^ f) X) :
    SylowFixerIsTwoGroup X := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff X f hf).mp hmodel
  exact fixer_of_equiv e (triality_fixer f hf)

/-- The canonical local construction transports the fixer bound to every large Ree model. -/
theorem ree_fixer (m : ℕ) (hm : 1 ≤ m)
    [IsSimpleGroup (ReeF4.Model m)] [Group.IsPerfect (ReeF4.Model m)] :
    SylowFixerIsTwoGroup (ReeF4.Model m) := by
  let d := canonicalLocalBlockInput m
  let : IsSimpleGroup d.fixedGroup := d.modelEquiv.isSimpleGroup
  let : Group.IsPerfect d.fixedGroup :=
    Group.IsPerfect.ofSurjective (f := d.modelEquiv.symm.toMonoidHom) d.modelEquiv.symm.surjective
  exact fixer_of_equiv d.modelEquiv.symm (ree_fixed_fixer hm d)

/-- Every genuine large Ree model witness supplies the intrinsic full Sylow fixer bound. -/
theorem ree_model_fixer {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] [Group.IsPerfect X] (hmodel : IsReeF4Model X) :
    SylowFixerIsTwoGroup X := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup (ReeF4.Model m) := e.symm.isSimpleGroup
  let : Group.IsPerfect (ReeF4.Model m) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact fixer_of_equiv e (ree_fixer m hm)

open Theory.GroupTheory
section Applications
variable {G : Type*} [Group G] [Finite G]
  (K L : Subgroup G) (T : Sylow 2 G)
  (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
  (hkind : IsQuasisimple K ∨ Nat.card K = 3)
  (hKN : K ≤ normalizer (L : Set G))
  (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥)

include hL hLK hkind hKN hd

/-- Discharge the Sylow-fixer premise of B.1.13 on the literal triality central quotient. -/
theorem triality_le_component {f : ℕ} (hf : 0 < f)
    (hmodel : IsTrialityGroupAt (2 ^ f) (L ⧸ center L)) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (triality_model_fixer hf hmodel) hd

/-- Discharge the Sylow-fixer premise of B.1.13 on the literal large Ree central quotient. -/
theorem ree_le_component (hmodel : IsReeF4Model (L ⧸ center L)) : K ≤ L := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (ree_model_fixer hmodel) hd
end Applications

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
