module

public import Stellmacher.Recognition.Parrott.SecondCentralizerLocalStructure
public import Stellmacher.Recognition.Parrott.SecondCentralizerFirstTransfer
public import Stellmacher.Recognition.Parrott.NormalizerFusionFromLocalData
public import Stellmacher.Recognition.Parrott.SecondCentralizerSecondTransfer
public import Stellmacher.Recognition.Parrott.SecondCentralizerContainmentAfterTransfer

/-!
# Identifying the second centralizer from local data

For N=N_G(F) and the supplied fixed involution v, the local calculation
identifies C_N(v) and its actual two-core. The two transfer steps supply
an actual Sylow subgroup with the omega and center identities that prove
C_G(v)≤N. Subgroup restriction is then an isomorphism and
transports the order, two-core image, and quotient to C_G(v). The outside-omega
transport and original-core fusion identify all remaining involutions with v,
retaining conjugators in C_G(z)∨N. The final assembly discharges containment
from the supplied normalizer and fixed-point data; the conditional transport
interfaces remain available separately.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, pp.682–683.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Transfer the proved local order, actual core, and quotient along an
established ambient centralizer containment. -/
public theorem second_centralizer_structure_of_containment
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v)
    (hcontain : centralizer ({v} : Set G) ≤ normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let C := centralizer ({v} : Set G)
    Nat.card C = 1536 ∧
      (pCore 2 C).map C.subtype = (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) ∧
      Nat.card (pCore 2 C) = 256 ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) := by
  intro N K C
  let B := C.subgroupOf N
  let e : B ≃* C := subgroupOfEquivOfLe hcontain
  obtain ⟨hcard, hcore, hcorecard, ⟨eqv⟩⟩ :=
    d.normalizer_fixed_centralizer_structure h hN hproper Q v hv hfix
  have he : (pCore 2 B).map e.toMonoidHom = pCore 2 C := pCore_map_iso 2 e
  refine ⟨(Nat.card_congr e.toEquiv).symm.trans hcard, ?_, ?_, ?_⟩
  · rw [← he, map_map]
    change ((pCore 2 B).map B.subtype).map N.subtype = _ at hcore
    have hcomp : C.subtype.comp e.toMonoidHom = N.subtype.comp B.subtype := by
      ext x
      rfl
    rw [hcomp]
    simpa only [map_map] using hcore
  · rw [← he, card_map_of_injective e.injective]
    exact hcorecard
  · exact ⟨(QuotientGroup.congr (pCore 2 B) (pCore 2 C) e he).symm.trans eqv⟩

/-- Every involution in the local second centralizer outside omega is conjugate
to the prescribed fixed point, with a conjugator in the original-centralizer
and second-normalizer join. -/
public theorem normalizer_fixed_outside_omega_fusion
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let H := centralizer ({z} : Set G)
    let L := H ⊔ N
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∀ u : G, u ∈ N ⊓ centralizer ({v} : Set G) → orderOf u = 2 → u ∉ W →
      ∃ l : L, (l : G) * v * (l : G)⁻¹ = u := by
  intro N K X D A W H L hCD v hv hfix u hu hu2 huW
  obtain ⟨g, hgJ, hgE⟩ :=
    d.normalizer_fixed_outside_omega_transport h hN hproper Q v hv hfix u hu hu2 huW
  have hg2 : orderOf ((g : G) * u * (g : G)⁻¹) = 2 :=
    ((MulAut.conj (g : G)).orderOf_eq u).trans hu2
  obtain ⟨l, hl⟩ := d.core_involution_fusion_in_join h hN hproper Q hCD v hv hfix
    _ hgJ hgE hg2
  let gL : L := ⟨g, (show N ≤ L from le_sup_right) g.property.1⟩
  refine ⟨gL⁻¹ * l, ?_⟩
  change ((g : G)⁻¹ * (l : G)) * v * ((g : G)⁻¹ * (l : G))⁻¹ = u
  calc
    _ = (g : G)⁻¹ * ((l : G) * v * (l : G)⁻¹) * (g : G) := by group
    _ = u := by rw [hl]; group

/-- Under ambient containment, the actual second two-core and quotient have
the prescribed orders and every involution outside that core is conjugate to v. -/
public theorem second_centralizer_identification_of_containment
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let C := centralizer ({v} : Set G)
    C ≤ N →
    Nat.card C = 1536 ∧
      (pCore 2 C).map C.subtype = (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) ∧
      Nat.card (pCore 2 C) = 256 ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) ∧
      (∀ u : G, u ∈ C → orderOf u = 2 → u ∉ (pCore 2 C).map C.subtype →
        IsConj v u) := by
  intro N K X D A hCD v hv hfix C hcontain
  obtain ⟨hcard, hcore, hcorecard, hquot⟩ :=
    d.second_centralizer_structure_of_containment h hN hproper Q v hv hfix hcontain
  refine ⟨hcard, hcore, hcorecard, hquot, ?_⟩
  intro u hu hu2 huCore
  obtain ⟨l, hl⟩ := d.normalizer_fixed_outside_omega_fusion h hN hproper Q hCD v hv hfix
    u ⟨hcontain hu, hu⟩ hu2 (by rwa [← hcore])
  exact isConj_iff.mpr ⟨(l : G), hl⟩

/-- The supplied local data force the ambient centralizer into the normalizer.
The second transfer constructs all the premises of the containment argument. -/
public theorem second_centralizer_le_normalizer_of_local_data
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
      centralizer ({v} : Set G) ≤ N := by
  intro N K X D A hCD v hv hfix
  obtain ⟨M, L, b, hMn, hMi, hMP, hLn, hLi,
    hbX, hb4, hb2, hbC, hbL, hYcard, hYO, hYZ, S, hS⟩ :=
    d.second_centralizer_second_transfer h hN hproper Q hCD v hv hfix
  exact d.second_centralizer_le_normalizer_of_second_transfer h hN hproper Q
    hCD v hv hfix M L hMn hMi hMP hLn hLi b hbX hb4 hb2 hbC hbL hYcard hYO hYZ S hS

/-- Identification of the ambient second involution centralizer from the
supplied local data: containment, order, actual two-core, quotient, and fusion.
No ambient containment or intermediate transfer premise remains. -/
public theorem second_centralizer_identification_of_local_data
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X := K.map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let C := centralizer ({v} : Set G)
    C ≤ N ∧
      Nat.card C = 1536 ∧
      (pCore 2 C).map C.subtype = (omega₁ K (p := 2)).map (N.subtype.comp K.subtype) ∧
      Nat.card (pCore 2 C) = 256 ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) ∧
      (∀ u : G, u ∈ C → orderOf u = 2 → u ∉ (pCore 2 C).map C.subtype →
        IsConj v u) := by
  intro N K X D A hCD v hv hfix C
  have hcontain := d.second_centralizer_le_normalizer_of_local_data h hN hproper Q
    hCD v hv hfix
  exact ⟨hcontain, d.second_centralizer_identification_of_containment h hN hproper Q
    hCD v hv hfix hcontain⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
