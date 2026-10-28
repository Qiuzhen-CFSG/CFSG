module

public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicRecognition
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore
public import Theory.AtlasPort.LinearGroups.G2.BinarySmallLocals
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Characteristic two in G₂ Sylow overgroups with nontrivial core

Borel–Tits places a Sylow overgroup with nontrivial two-core in a root
parabolic. Each full parabolic has characteristic two, as do the two
parabolics restricted to the actual binary derived group. Characteristic
two passes to subgroups containing their Sylow subgroup. Conjugacy and
subgroup equivalences give the result in the original marking.

Source: Aschbacher–Smith, 15.3.28, printed p.1131, and the
defining-characteristic normalizer argument of Theorem 0.1.2(1).
Root and hexagon facts use the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

public section
open Subgroup
namespace Atlas.G2.SylowOvergroupCharacteristic

private theorem restriction {A : Type*} [Group A] [Finite A]
    (Q : Sylow 2 A) (H P : Subgroup A)
    (hQH : (Q : Subgroup A) ≤ H) (hHP : H ≤ P)
    (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have h := centralizer_pCore_le_of_sylow_le (Q.subtype (hQH.trans hHP))
    (H.subgroupOf P) (fun _ hx => hQH hx) hP
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe hHP)).mp h

open LieParabolicSetup

/-- Full split-octonion carrier, including its full binary specialization. -/
theorem full {F : Type*} [Field F] [Finite F] [CharP F 2]
    (Q : Sylow 2 (Model F)) (H : Subgroup (Model F))
    (hQH : (Q : Subgroup (Model F)) ≤ H) (hcore : pCore 2 H ≠ ⊥) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  let R := (pCore 2 H).map H.subtype
  have hR : R ≠ ⊥ := fun h => hcore
    (((pCore 2 H).map_eq_bot_iff_of_injective H.subtype_injective).mp h)
  have hHR : H ≤ normalizer (R : Set (Model F)) := by
    intro h hh
    apply (pCore 2 H).le_normalizer_map H.subtype
    exact ⟨⟨h, hh⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  obtain ⟨g, hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic R hR
    (pCore_isPGroup.map H.subtype)
  let e := MulAut.conj g
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ' : (Q' : Subgroup (Model F)) ≤ H.map e.toMonoidHom := map_mono hQH
  have hc : centralizer (pCore 2 (H.map e.toMonoidHom) : Set (H.map e.toMonoidHom)) ≤
      pCore 2 (H.map e.toMonoidHom) := by
    rcases hg with hg | hg
    · exact restriction Q' _ parabolic₁ hQ' ((map_mono hHR).trans hg)
        EvenLocal.parabolic₁_centralizer_pCore
    · exact restriction Q' _ parabolic₂ hQ' ((map_mono hHR).trans hg)
        EvenLocal.parabolic₂_centralizer_pCore
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap H)).mpr hc

/-- The proper commutator carrier G₂(2)′, with its Sylow of order 32. -/
theorem binary_derived
    (Q : Sylow 2 (commutator (Model (ZMod 2))))
    (H : Subgroup (commutator (Model (ZMod 2))))
    (hQH : (Q : Subgroup (commutator (Model (ZMod 2)))) ≤ H)
    (hcore : pCore 2 H ≠ ⊥) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  obtain ⟨e, i, _, hH⟩ := SylowParabolicRecognition.exists_aligned_parabolic_of_twoCore
    (MulEquiv.refl _) Q H hQH hcore
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ' : (Q' : Subgroup (commutator (Model (ZMod 2)))) ≤ H.map e.toMonoidHom :=
    map_mono hQH
  have hzero : SylowParabolicRecognition.rootParabolic (F := ZMod 2) 0 =
      BinaryParabolicPair.derivedFirst := by
    change parabolic₁.subgroupOf (commutator (Model (ZMod 2))) = _
    rw [parabolic₁_binary]
    rfl
  have hone : SylowParabolicRecognition.rootParabolic (F := ZMod 2) 1 =
      BinaryParabolicPair.derivedSecond := rfl
  have hp : centralizer (pCore 2 (SylowParabolicRecognition.rootParabolic
      (F := ZMod 2) i) : Set (SylowParabolicRecognition.rootParabolic (F := ZMod 2) i)) ≤
      pCore 2 (SylowParabolicRecognition.rootParabolic (F := ZMod 2) i) := by
    fin_cases i
    · exact hzero.symm ▸ BinaryParabolicPair.derivedFirst_centralizer_pCore
    · exact hone.symm ▸ BinaryParabolicPair.derivedSecond_centralizer_pCore
  have hc := restriction Q' _ _ hQ' hH hp
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap H)).mpr hc

end Atlas.G2.SylowOvergroupCharacteristic
