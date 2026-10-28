module
public import Theory.Representation.BinaryPermutation.FiveOrbits
public import Theory.Representation.BinaryPermutationMulAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# The S₅-module centralizer orbit branch of original 13.1.12

The literal conjugation marking identifies C_M(u) with the pullback of a
vector stabilizer in the binary five-point core. Its index in M is five
or ten. If C_T(u) is Sylow in C_M(u), the two Sylow index factorizations
show that [T:C_T(u)] divides this orbit index and is a power of two.
Consequently [T:C_T(u)]≤2. A vector moved by T must lie in the
nonsingular orbit, where the actual alternating centralizer image is S₃.

Both the core and natural deleted-module versions retain the exact
ambient subgroups, centralizer, quotient homomorphism and conjugation
marking. The source marking and local Sylow selection come from the
preceding 13.1.10 case; orbit size and stabilizer structure are proved.
These results supply the S₅ orbit/index and nonabelian-image inputs of
13.1.12, not the later escaping-component exclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.1.10(2)
and the proof of 13.1.12(1–2), printed pp.872–873.
-/

public noncomputable section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerOrbits.SymmetricFive
open Chapter1
variable {G : Type*} [Group G] [Finite G]

private theorem relative_sylow_odd {S H : Subgroup G} (h : IsSylowIn 2 S H) :
    ¬ 2 ∣ S.relIndex H := by
  obtain ⟨P,rfl⟩ := h
  change ¬2 ∣ (((P : Subgroup H).map H.subtype).subgroupOf H).index
  change ¬ 2 ∣ (((P : Subgroup H).map H.subtype).comap H.subtype).index
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  exact P.not_dvd_index

/-- The Sylow stabilizer index divides the actual ambient orbit index. -/
theorem sylow_intersection_index_dvd (T M C : Subgroup G)
    (hT : IsSylowIn 2 T M) (hlocal : IsSylowIn 2 (T ⊓ C) (M ⊓ C)) :
    C.relIndex T ∣ C.relIndex M := by
  have hpT := (isSylowIn_iff.mp hT).1
  have hTM := (isSylowIn_iff.mp hT).2.1
  let S := T ⊓ C
  have hS : S ≤ M ⊓ C := inf_le_inf_right C hTM
  have heq : S.relIndex T * T.relIndex M = S.relIndex (M ⊓ C) * (M ⊓ C).relIndex M :=
    (relIndex_mul_relIndex S T M inf_le_left hTM).trans
      (relIndex_mul_relIndex S (M ⊓ C) M hS inf_le_left).symm
  obtain ⟨n,hn⟩ := hpT.index (S.subgroupOf T)
  change S.relIndex T = 2 ^ n at hn
  have hcop : Nat.Coprime (S.relIndex T) (S.relIndex (M ⊓ C)) := by
    rw [hn]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr (relative_sylow_odd hlocal)).pow_left n
  have hd : S.relIndex T ∣ (M ⊓ C).relIndex M :=
    hcop.dvd_of_dvd_mul_left ⟨T.relIndex M,heq.symm⟩
  simpa only [S,inf_relIndex_left] using hd

/-- A locally Sylow stabilizer in an orbit with two-part at most two
has index at most two in the chosen Sylow subgroup. -/
theorem sylow_intersection_index_le_two (T M C : Subgroup G)
    (hT : IsSylowIn 2 T M) (hlocal : IsSylowIn 2 (T ⊓ C) (M ⊓ C))
    (hfour : ¬ 4 ∣ C.relIndex M) : C.relIndex T ≤ 2 := by
  have hd := sylow_intersection_index_dvd T M C hT hlocal
  obtain ⟨n,hn⟩ := (isSylowIn_iff.mp hT).1.index (C.subgroupOf T)
  change C.relIndex T = 2 ^ n at hn
  have hbound : n ≤ 1 := by
    by_contra h
    have hn2 : 2 ≤ n := by omega
    apply hfour
    have hdiv : 4 ∣ C.relIndex T := by rw [hn]; exact pow_dvd_pow 2 hn2
    exact hdiv.trans hd
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hbound

variable (M U : Subgroup G) (hn : M ≤ normalizer (U : Set G))
    (q : M →* FiveOrbits.S5) (hq : Function.Surjective q)
    (e : U ≃* Multiplicative FiveOrbits.Space)
    (he : ∀ (m : M) (v : U),
      e (U.normalizerMonoidHom (inclusion hn m) v) =
        Multiplicative.ofAdd (FiveOrbits.rho (q m) (e v).toAdd))

include hn he

omit [Finite G] in
/-- The model stabilizer is the image of the literal element centralizer. -/
theorem centralizer_subgroupOf_eq (u : U) :
    (centralizer ({(u : G)} : Set G)).subgroupOf M =
      (FiveOrbits.stabilizer (e u).toAdd).comap q := by
  ext m
  change (m : G) ∈ centralizer ({(u : G)} : Set G) ↔
    FiveOrbits.rho (q m) (e u).toAdd = (e u).toAdd
  rw [mem_centralizer_singleton_iff]
  have hmodel := congrArg Multiplicative.toAdd (he m u)
  change (e (U.normalizerMonoidHom (inclusion hn m) u)).toAdd =
    FiveOrbits.rho (q m) (e u).toAdd at hmodel
  constructor
  · intro hc
    rw [← hmodel]
    apply congrArg (fun v : U => (e v).toAdd)
    apply Subtype.ext
    change (m : G) * (u : G) * (m : G)⁻¹ = (u : G)
    rw [hc,mul_inv_cancel_right]
  · intro hc
    have hu : U.normalizerMonoidHom (inclusion hn m) u = u :=
      e.injective (congrArg Multiplicative.ofAdd (hmodel.trans hc))
    have huv := congrArg Subtype.val hu
    change (m : G) * (u : G) * (m : G)⁻¹ = (u : G) at huv
    exact mul_inv_eq_iff_eq_mul.mp huv

include hq

omit [Finite G] in
/-- The original centralizer has the concrete index five or ten. -/
theorem centralizer_relative_index (u : U) (hu : u ≠ 1) :
    (centralizer ({(u : G)} : Set G)).relIndex M =
      if FiveOrbits.weight (e u).toAdd = 2 then 10 else 5 := by
  change ((centralizer ({(u : G)} : Set G)).subgroupOf M).index = _
  rw [centralizer_subgroupOf_eq M U hn q e he u,
    Subgroup.index_comap_of_surjective _ hq]
  exact FiveOrbits.stabilizer_index _ (by
    intro hz
    apply hu
    exact e.injective ((congrArg Multiplicative.ofAdd hz).trans (map_one e).symm))

/-- Source 13.1.12(2) in the marked S₅-module case, for the actual Sylow
and literal centralizer of u. -/
theorem source_symmetricFive_centralizer_index (T : Subgroup G)
    (hT : IsSylowIn 2 T M) (u : U) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 (T ⊓ centralizer ({(u : G)} : Set G))
      (M ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex T ≤ 2 := by
  apply sylow_intersection_index_le_two T M _ hT hlocal
  rw [centralizer_relative_index M U hn q hq e he u hu]
  split_ifs <;> decide


/-- A vector which is not fixed by the Sylow subgroup lies in the nonsingular orbit. -/
theorem source_symmetricFive_nonsingular (T : Subgroup G)
    (hT : IsSylowIn 2 T M) (u : U) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 (T ⊓ centralizer ({(u : G)} : Set G))
      (M ⊓ centralizer ({(u : G)} : Set G)))
    (hmove : ¬ T ≤ centralizer ({(u : G)} : Set G)) :
    FiveGeometry.form (e u).toAdd ≠ 0 := by
  apply (FiveOrbits.nonsingular_iff_weight_two _).mpr
  by_contra hw
  have hi := source_symmetricFive_centralizer_index M U hn q hq e he T hT u hu hlocal
  have hd := sylow_intersection_index_dvd T M (centralizer ({(u : G)} : Set G)) hT hlocal
  rw [centralizer_relative_index M U hn q hq e he u hu,if_neg hw] at hd
  have hone : (centralizer ({(u : G)} : Set G)).relIndex T = 1 := by
    have hp : 0 < (centralizer ({(u : G)} : Set G)).relIndex T := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hsmall : (centralizer ({(u : G)} : Set G)).relIndex T = 1 ∨
      (centralizer ({(u : G)} : Set G)).relIndex T = 2 := by omega
    rcases hsmall with h | h
    · exact h
    · rw [h] at hd; norm_num at hd
  exact hmove (relIndex_eq_one.mp hone)

omit hq [Finite G] in
/-- The image of the actual alternating centralizer is the concrete A₅ stabilizer. -/
theorem alternating_centralizer_image (L : Subgroup G)
    (hL : (L.subgroupOf M).map q = alternatingGroup (Fin 5)) (u : U) :
    ((L ⊓ centralizer ({(u : G)} : Set G)).subgroupOf M).map q =
      (FiveOrbits.evenStabilizer (e u).toAdd).map (alternatingGroup (Fin 5)).subtype := by
  have hC := centralizer_subgroupOf_eq M U hn q e he u
  apply le_antisymm
  · rintro g ⟨m,hm,rfl⟩
    have ha : q m ∈ alternatingGroup (Fin 5) := hL ▸ mem_map_of_mem q hm.1
    have hf : FiveOrbits.rho (q m) (e u).toAdd = (e u).toAdd := by
      have hh : m ∈ (centralizer ({(u : G)} : Set G)).subgroupOf M := hm.2
      rwa [hC] at hh
    exact ⟨⟨q m,ha⟩,hf,rfl⟩
  · rintro g ⟨a,ha,rfl⟩
    obtain ⟨m,hm,hma⟩ := show a.val ∈ (L.subgroupOf M).map q from hL.symm ▸ a.property
    have hf : m ∈ (centralizer ({(u : G)} : Set G)).subgroupOf M := by
      rw [hC]
      change FiveOrbits.rho (q m) (e u).toAdd = (e u).toAdd
      rw [hma]
      exact ha
    exact ⟨m,⟨hm,hf⟩,hma⟩

omit hq in
/-- The actual alternating centralizer image is S₃ at a nonsingular vector. -/
noncomputable def alternatingCentralizerImageEquivS3 (L : Subgroup G)
    (hL : (L.subgroupOf M).map q = alternatingGroup (Fin 5))
    (u : U) (hu : FiveGeometry.form (e u).toAdd ≠ 0) :
    (((L ⊓ centralizer ({(u : G)} : Set G)).subgroupOf M).map q) ≃*
      Equiv.Perm (Fin 3) :=
  (MulEquiv.subgroupCongr (alternating_centralizer_image M U hn q e he L hL u)).trans
    (((FiveOrbits.evenStabilizer (e u).toAdd).equivMapOfInjective
      (alternatingGroup (Fin 5)).subtype Subtype.val_injective).symm.trans
        (FiveOrbits.evenStabilizerEquivS3 _ ((FiveOrbits.nonsingular_iff_weight_two _).mp hu)))

/-- The S₅ branch supplies the original index bound and its actual nonabelian S₃
centralizer image whenever u is not two-central. -/
theorem source_symmetricFive_orbit_and_stabilizer (T L : Subgroup G)
    (hT : IsSylowIn 2 T M)
    (hL : (L.subgroupOf M).map q = alternatingGroup (Fin 5))
    (u : U) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 (T ⊓ centralizer ({(u : G)} : Set G))
      (M ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex T ≤ 2 ∧
      (¬ T ≤ centralizer ({(u : G)} : Set G) →
        Nonempty ((((L ⊓ centralizer ({(u : G)} : Set G)).subgroupOf M).map q) ≃*
          Equiv.Perm (Fin 3))) := by
  refine ⟨source_symmetricFive_centralizer_index M U hn q hq e he T hT u hu hlocal,?_⟩
  intro hm
  exact ⟨alternatingCentralizerImageEquivS3 M U hn q e he L hL u
    (source_symmetricFive_nonsingular M U hn q hq e he T hT u hu hlocal hm)⟩


omit hq [Finite G] in
/-- The actual alternating centralizer image is nonabelian in the nonsingular case. -/
theorem alternating_centralizer_image_not_commutative (L : Subgroup G)
    (hL : (L.subgroupOf M).map q = alternatingGroup (Fin 5))
    (u : U) (hu : FiveGeometry.form (e u).toAdd ≠ 0) :
    ¬ IsMulCommutative (((L ⊓ centralizer ({(u : G)} : Set G)).subgroupOf M).map q) := by
  intro hc
  let a := alternatingCentralizerImageEquivS3 M U hn q e he L hL u hu
  have hab := (isMulCommutative_iff.mp hc)
    (a.symm (Equiv.swap 0 1)) (a.symm (Equiv.swap 1 2))
  have hh := congrArg a hab
  simp only [map_mul,a.apply_symm_apply] at hh
  have hn : (Equiv.swap 0 1 : Equiv.Perm (Fin 3))*Equiv.swap 1 2 ≠
      Equiv.swap 1 2*Equiv.swap 0 1 := by decide
  exact hn hh

omit e he in
/-- The same source conclusion using the library's literal natural deleted module. -/
theorem source_symmetricFive_natural_orbit_and_stabilizer
    (en : U ≃* Multiplicative (natural (Fin 5)))
    (hen : ∀ (m : M) (v : U),
      en (U.normalizerMonoidHom (inclusion hn m) v) =
        naturalMulAction (Fin 5) (q m) (en v))
    (T L : Subgroup G) (hT : IsSylowIn 2 T M)
    (hL : (L.subgroupOf M).map q = alternatingGroup (Fin 5))
    (u : U) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 (T ⊓ centralizer ({(u : G)} : Set G))
      (M ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex T ≤ 2 ∧
      (¬ T ≤ centralizer ({(u : G)} : Set G) →
        Nonempty ((((L ⊓ centralizer ({(u : G)} : Set G)).subgroupOf M).map q) ≃*
          Equiv.Perm (Fin 3)) ∧
        ¬ IsMulCommutative (((L ⊓ centralizer ({(u : G)} : Set G)).subgroupOf M).map q)) := by
  let c := coreEquivNatural (Fin 5) (by decide)
  let f : U ≃* Multiplicative FiveOrbits.Space := en.trans c.symm.toAddEquiv.toMultiplicative
  have hf : ∀ (m : M) (v : U),
      f (U.normalizerMonoidHom (inclusion hn m) v) =
        Multiplicative.ofAdd (FiveOrbits.rho (q m) (f v).toAdd) := by
    intro m v
    change Multiplicative.ofAdd (c.symm (en (U.normalizerMonoidHom (inclusion hn m) v)).toAdd) = _
    rw [hen,naturalMulAction_apply]
    apply congrArg Multiplicative.ofAdd
    apply c.injective
    rw [c.apply_symm_apply]
    have hh := coreEquivNatural_equivariant (Fin 5) (by decide) (q m) (f v).toAdd
    change c (FiveOrbits.rho (q m) (f v).toAdd) =
      naturalRepresentation (Fin 5) (q m) (c (c.symm (en v).toAdd)) at hh
    rw [c.apply_symm_apply] at hh
    exact hh.symm
  refine ⟨source_symmetricFive_centralizer_index M U hn q hq f hf T hT u hu hlocal,?_⟩
  intro hm
  have hns := source_symmetricFive_nonsingular M U hn q hq f hf T hT u hu hlocal hm
  exact ⟨⟨alternatingCentralizerImageEquivS3 M U hn q f hf L hL u hns⟩,
    alternating_centralizer_image_not_commutative M U hn q f hf L hL u hns⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerOrbits.SymmetricFive
