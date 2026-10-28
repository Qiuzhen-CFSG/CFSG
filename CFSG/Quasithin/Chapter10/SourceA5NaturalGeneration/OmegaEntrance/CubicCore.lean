module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.OmegaEntrance.FirstSection
public import Theory.GroupTheory.ConjugateSpanOrder
public import CFSG.Quasithin.Chapter3.Section02.CenterObstruction
public import Theory.Representation.BinaryConjugationSection.OmegaDiagonal
/-!
# Cubic detection by the original Sylow omega-center

The half-Sylow fixed-span identity supplies a noncentral vector in the
original moved factor. Its index-two diagonal lies in the Sylow omega-center.
The original natural coordinates and cubic fixed-vector calculation therefore
detect every order-three element of the original component orbit, including
the second quotient factor by the actual Sylow conjugation. Elementary-three
Hall centralizers and the required entrance commutator follow immediately.
The next source module discharges the fixed-span identity.

Source: Aschbacher–Smith10.1.2(5), printed p.742.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
  (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
  {K : Type*} [Field K] [CharP K 2]
local instance omegaEntranceCubicAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2
local instance omegaEntranceCubicElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable (f : alternatingGroup (Fin 5) ≃* SL(2,K))
  (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))

include D e hn ht htn hcross f n

set_option backward.isDefEq.respectTransparency false in
theorem source_original_first_cubic_not_centralizes_omegaCenter
    (hfixed : conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)) L = ⁅D.fullModule,L⁆)
    (b : localOrbit T L)
    (hb : orderOf (originalA5ProductProjection D e hn ht htn b).1 = 3) :
    (b:G) ∉ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  have h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
    Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal
  let R := localOrbit T L
  let W := ⁅D.fullModule,L⁆
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let nR := source_original_natural_first_orbit_section D e hn ht htn hcross f n
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hWT : W ≤ (T : Subgroup G) :=
    hWV.trans (D.fullModule_le_sylow h127)
  have hWS : W ≤ S := le_inf hWT
    (n.section_le.trans L.le_normalizer)
  have hspan : conjugateSpanBy (W ⊓ centralizer (S : Set G)) L = W := hfixed
  have hex : ∃ w : W, (w:G) ∈ centralizer (S : Set G) ∧ nR.coordinates w ≠ 1 := by
    by_contra! h
    have hfix : W ⊓ centralizer (S : Set G) ≤ sourceMovedFixed D := by
      intro w hw
      exact (nR.coordinates_eq_one_iff ⟨w,hw.1⟩).mp (h ⟨w,hw.1⟩ hw.2)
    have hLZ : L ≤ normalizer (sourceMovedFixed D : Set G) :=
      (le_inf L.le_normalizer n.normalized).trans (source_original_moved_fixed_normalizer D)
    have hWZ : W ≤ sourceMovedFixed D := hspan.ge.trans (conjugateSpanBy_le hfix hLZ)
    have he : ⁅W,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hWZ.trans inf_le_right)
    exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans he)
  obtain ⟨w,hwS,hwn⟩ := hex
  have hwomega : (w:G) ∈ omegaOneCenterAmbient S :=
    (mem_omegaOneCenterAmbient_iff S w).mpr
      ⟨hWS w.property,elemPow_eq_one_of_isElementaryAbelian (p:=2) (w:G) w.property,hwS⟩
  have hVt : t*(w:G)*t⁻¹ ∈ D.fullModule :=
    (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht)) w).mp (hWV w.property)
  let : IsElementaryAbelian 2 D.fullModule :=
    D.fullModule_elementary h127
  have hc : Commute (w:G) (t*w*t⁻¹) := congrArg D.fullModule.subtype
    (mul_comm (⟨w,hWV w.property⟩ : D.fullModule) ⟨t*w*t⁻¹,hVt⟩)
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  have hRWt : R ≤ normalizer (W.map (MulAut.conj t).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) nR.normalized
    rwa [hRt,map_normalizer_eq_of_bijective W (MulAut.conj t).bijective] at hh
  have hinter : W ⊓ W.map (MulAut.conj t).toMonoidHom ≤ sourceMovedFixed D :=
    le_inf inf_le_left (inf_le_right.trans hcross)
  have hiS : S.relIndex (T : Subgroup G) = 2 := by
    change ((T : Subgroup G) ⊓ normalizer (L : Set G)).relIndex (T : Subgroup G) = 2
    rw [inf_relIndex_left]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  exact BinaryConjugationSection.natural_cubic_not_centralizes_omegaCenter_of_diagonal
    (S := S) (T := (T : Subgroup G)) _ nR inf_le_left hiS
    t ht (fun htS => htn htS.2) hRWt hinter w hwomega hc hwn b
    ((f.orderOf_eq _).trans hb)

/-- The actual original two-factor quotient detects every cubic element. -/
theorem source_original_cubic_not_centralizes_omegaCenter
    (hfixed : conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)) L = ⁅D.fullModule,L⁆)
    (b : localOrbit T L) (hb : orderOf b = 3) :
    (b:G) ∉ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let q := originalA5ProductProjection D e hn ht htn
  have hqne : q b ≠ 1 := by
    intro hz
    have hcore : b ∈ pCore 2 (localOrbit T L) := by
      rw [←originalA5ProductProjection_ker D e hn ht htn]
      exact hz
    have hord : orderOf (⟨b,hcore⟩ : pCore 2 (localOrbit T L)) = 3 := by
      simpa only [orderOf_mk] using hb
    have hc := (pCore_isPGroup (p:=2) (G:=localOrbit T L)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨b,hcore⟩ : pCore 2 (localOrbit T L))
    rw [hord] at hc
    norm_num at hc
  have hcases : orderOf (q b).1 = 3 ∨ orderOf (q b).2 = 3 := by
    have h₁ : orderOf (q b).1 ∣ 3 := by
      have hh := orderOf_map_dvd ((MonoidHom.fst _ _).comp q) b
      change orderOf (q b).1 ∣ orderOf b at hh
      rwa [hb] at hh
    have h₂ : orderOf (q b).2 ∣ 3 := by
      have hh := orderOf_map_dvd ((MonoidHom.snd _ _).comp q) b
      change orderOf (q b).2 ∣ orderOf b at hh
      rwa [hb] at hh
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h₁ with h₁ | h₁
    · rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h₂ with h₂ | h₂
      · exact (hqne (Prod.ext (orderOf_eq_one_iff.mp h₁) (orderOf_eq_one_iff.mp h₂))).elim
      · exact Or.inr h₂
    · exact Or.inl h₁
  rcases hcases with hfirst | hsecond
  · exact source_original_first_cubic_not_centralizes_omegaCenter D e hn ht htn hcross f n hfixed b hfirst
  · intro hbZ
    let b' := originalOrbitConjugation ht b
    have hb' : orderOf (q b').1 = 3 := by
      rw [show q b' = (originalA5ConjugationTwist D e hn ht (q b).2,(q b).1) from
        originalA5ProductProjection_conjugate D e hn ht htn b]
      exact ((originalA5ConjugationTwist D e hn ht).orderOf_eq _).trans hsecond
    apply source_original_first_cubic_not_centralizes_omegaCenter D e hn ht htn hcross f n hfixed b' hb'
    intro z hz
    have hzT := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    have hzt := hzT.2.2 t ht
    have hzb := hbZ z hz
    change z*(t*(b:G)*t⁻¹) = (t*(b:G)*t⁻¹)*z
    have htiz : t⁻¹*z = z*t⁻¹ := (show Commute t z from hzt).inv_left.eq
    calc
      z*(t*(b:G)*t⁻¹) = (z*t)*(b:G)*t⁻¹ := by group
      _ = (t*z)*(b:G)*t⁻¹ := by rw [hzt]
      _ = t*(z*(b:G))*t⁻¹ := by group
      _ = t*((b:G)*z)*t⁻¹ := by rw [hzb]
      _ = (t*(b:G))*(z*t⁻¹) := by group
      _ = (t*(b:G))*(t⁻¹*z) := by rw [htiz]
      _ = (t*(b:G)*t⁻¹)*z := by group

/-- Actual elementary-three Hall subgroups of the original orbit act
faithfully on the Sylow omega-center. -/
theorem source_original_elementary_three_omega_centralizer_eq_bot
    (hfixed : conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)) L = ⁅D.fullModule,L⁆)
    (B : Subgroup G) [IsElementaryAbelian 3 B] (hBR : B ≤ localOrbit T L) :
    B ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro b hb
  by_contra hne
  have hbne : b ≠ 1 := hne
  have ho : orderOf b = 3 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb.1) hbne
  exact source_original_cubic_not_centralizes_omegaCenter D e hn ht htn hcross f n hfixed
    ⟨b,hBR hb.1⟩ (by simpa only [orderOf_mk] using ho) hb.2

/-- A nontrivial actual Hall subgroup in H forces the Omega-center entrance
required before the selected E.2.3 source can be invoked. -/
theorem source_original_omega_commutator_ne_bot_of_three_hall
    (hfixed : conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G)) L = ⁅D.fullModule,L⁆)
    (B H : Subgroup G) [IsElementaryAbelian 3 B]
    (hBR : B ≤ localOrbit T L) (hBH : B ≤ H) (hB : B ≠ ⊥) :
    ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥ := by
  intro hz
  have hBC : B ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) :=
    hBH.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  apply hB
  exact (inf_eq_left.mpr hBC).symm.trans
    (source_original_elementary_three_omega_centralizer_eq_bot D e hn ht htn hcross f n hfixed B hBR)

end CFSG.Quasithin.Chapter10
