module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.LocalSubgroups
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.SylowPlacement
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# Intrinsic max4 cores in the conjugates used by Sylow placement

Conjugation carries O2(max4) to the intrinsic two-core of the actual conjugate,
and carries its center to that core's actual center. The equivalences retain
the ambient inclusions. Any proved outside-core involution marking therefore
transports to the conjugate containing a prescribed ambient Sylow subgroup,
with explicit Sylow-center witnesses.

Source: the choice of M* over S* in Aschbacher--Smith I.2.2(7), printed
pp.412--413. The fixed-subgroup outside-core marking remains an explicit input;
transport does not prove the fusion calculation in J.2.6(2).
-/

open Subgroup
open Rudvalis Rudvalis.SylowOvergroups Rudvalis.CoreQuotients
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open Theory.GroupTheory.DoubleCoverCentralizer

namespace Rudvalis.CoveringIncidence

@[expose] public def conjugateMax4Core (g : Model) : Subgroup Model :=
  (pCore 2 (conjugateMax4 g)).map (conjugateMax4 g).subtype

@[expose] public def conjugateMax4CoreCenter (g : Model) : Subgroup Model :=
  (center (conjugateMax4Core g)).map (conjugateMax4Core g).subtype

public theorem conjugateMax4Core_eq_map (g : Model) :
    conjugateMax4Core g = max4Core.map (MulAut.conj g).toMonoidHom := by
  let e : max4 ≃* conjugateMax4 g := (MulAut.conj g).subgroupMap max4
  unfold conjugateMax4Core
  rw [← pCore_map_iso 2 e, map_map]
  change _ = ((pCore 2 max4).map max4.subtype).map (MulAut.conj g).toMonoidHom
  rw [map_map]
  rfl

public noncomputable def conjugateMax4CoreEquiv (g : Model) :
    max4Core ≃* conjugateMax4Core g :=
  ((MulAut.conj g).subgroupMap max4Core).trans
    (MulEquiv.subgroupCongr (conjugateMax4Core_eq_map g).symm)

@[simp] public theorem conjugateMax4CoreEquiv_apply (g : Model) (x : max4Core) :
    (conjugateMax4CoreEquiv g x : Model) = g * (x : Model) * g⁻¹ := by rfl

public theorem conjugateMax4CoreCenter_eq_map (g : Model) :
    conjugateMax4CoreCenter g = max4CoreCenter.map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · rintro x ⟨z, hz, rfl⟩
    let w := (centerCongr (conjugateMax4CoreEquiv g)).symm ⟨z, hz⟩
    refine ⟨(w : max4Core), ⟨(w : max4Core), w.property, rfl⟩, ?_⟩
    have he := (centerCongr (conjugateMax4CoreEquiv g)).apply_symm_apply ⟨z, hz⟩
    exact congrArg (fun c : center (conjugateMax4Core g) => ((c : conjugateMax4Core g) : Model)) he
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    let w := centerCongr (conjugateMax4CoreEquiv g) ⟨z, hz⟩
    exact ⟨(w : conjugateMax4Core g), w.property, rfl⟩

public theorem conjugate_center_eq_marked (g : Model) (hcenter : max4CoreCenter = elementary 2) :
    conjugateMax4CoreCenter g = (elementary 2).map (MulAut.conj g).toMonoidHom := by
  rw [conjugateMax4CoreCenter_eq_map, hcenter]

public theorem outside_core_twoCentral_conjugate
    (hmark : ∀ x : Model, x ∈ max4 → x ∉ max4Core → orderOf x = 2 → TwoCentral x)
    (g : Model) (x : Model) (hx : x ∈ conjugateMax4 g)
    (hxP : x ∉ conjugateMax4Core g) (horder : orderOf x = 2) : TwoCentral x := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hyP : y ∉ max4Core := by
    intro h
    apply hxP
    rw [conjugateMax4Core_eq_map]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom h
  have hyorder : orderOf y = 2 := by
    change orderOf (MulAut.conj g y) = 2 at horder
    rwa [(MulAut.conj g).orderOf_eq] at horder
  exact (hmark y hy hyP hyorder).map (MulAut.conj g)

public theorem exists_marked_conjugateMax4_over_sylow
    (hmark : ∀ x : Model, x ∈ max4 → x ∉ max4Core → orderOf x = 2 → TwoCentral x)
    (S : Sylow 2 Model) :
    ∃ g : Model, (S : Subgroup Model) ≤ conjugateMax4 g ∧
      ∀ x : Model, x ∈ conjugateMax4 g → x ∉ conjugateMax4Core g → orderOf x = 2 →
        ∃ T : Sylow 2 Model, ∃ hxT : x ∈ T, (⟨x, hxT⟩ : T) ∈ center T := by
  obtain ⟨g, hg⟩ := exists_conjugateMax4_over_sylow S
  exact ⟨g, hg, outside_core_twoCentral_conjugate hmark g⟩

end Rudvalis.CoveringIncidence
