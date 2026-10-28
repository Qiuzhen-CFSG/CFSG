module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The actual iterated core and residual in 13.6.26

The intrinsic subgroup is the preimage of O_p(H/O₂(H)) under the original
quotient map. Its ambient image is O_{2,p}(H). The residual used by the
source is O^{p′}, whose quotient has order prime to p. Characteristicity
supplies relative normality, and a trivial residual forces the quotient
p-core to be trivial, giving O_{2,p}(H) = O₂(H).

These constructions intentionally do not use the distinct legacy objects
in `TerminalSource`. Source: Aschbacher–Smith, combined manuscript
(1 March 2004), Lemma 13.6.26, printed p.934.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters

open Subgroup

/-- The intrinsic quotient-preimage convention for O_{2,p}. -/
def twoPCore (p : ℕ) (H : Type*) [Group H] : Subgroup H :=
  (pCore p (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))

instance twoPCore_characteristic (p : ℕ) (H : Type*) [Group H] :
    (twoPCore p H).Characteristic :=
  Subgroup.Characteristic.comap_quotient_mk inferInstance

instance twoPCore_normal (p : ℕ) (H : Type*) [Group H] :
    (twoPCore p H).Normal := inferInstance

variable {G : Type*} [Group G]

/-- O_{2,p}(H), embedded into the original ambient group. -/
def O2p (H : Subgroup G) (p : ℕ) : Subgroup G :=
  (twoPCore p H).map H.subtype

/-- X in the proof of 13.6.26: the embedded prime-to-p residual. -/
def O2pResidual (H : Subgroup G) (p : ℕ) : Subgroup G :=
  (primeToResidual p (O2p H p)).map (O2p H p).subtype

theorem O2p_le (H : Subgroup G) (p : ℕ) : O2p H p ≤ H := map_subtype_le _

theorem twoCore_le_O2p (H : Subgroup G) (p : ℕ) : H.pCoreIn 2 ≤ O2p H p := by
  apply map_mono
  intro x hx
  change QuotientGroup.mk' (pCore 2 H) x ∈ pCore p (H ⧸ pCore 2 H)
  have hq : QuotientGroup.mk' (pCore 2 H) x = 1 :=
    (QuotientGroup.eq_one_iff (N := pCore 2 H) x).mpr hx
  rw [hq]
  exact one_mem _

theorem le_normalizer_O2p (H : Subgroup G) (p : ℕ) :
    H ≤ normalizer (O2p H p : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (twoPCore p H))

theorem O2pResidual_le (H : Subgroup G) (p : ℕ) : O2pResidual H p ≤ O2p H p :=
  map_subtype_le _

theorem le_normalizer_O2pResidual (H : Subgroup G) (p : ℕ) :
    H ≤ normalizer (O2pResidual H p : Set G) :=
  (le_normalizer_O2p H p).trans
    (normalizer_le_normalizer_characteristic_image (O2p H p)
      (primeToResidual p (O2p H p)))

variable [Finite G]

/-- The iterated core is solvable: both its kernel and quotient are p-groups. -/
theorem O2p_isSolvable (H : Subgroup G) (p : ℕ) [Fact p.Prime] :
    Group.IsSolvable (O2p H p) := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (pCore p (H ⧸ pCore 2 H)) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 H)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable (twoPCore p H) :=
    isSolvable_comap_of_solvable_ker (QuotientGroup.mk' (pCore 2 H)) _
  exact Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective (twoPCore p H))

/-- The actual residual is a subgroup of that solvable iterated core. -/
theorem O2pResidual_isSolvable (H : Subgroup G) (p : ℕ) [Fact p.Prime] :
    Group.IsSolvable (O2pResidual H p) := by
  let := O2p_isSolvable H p
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (O2pResidual_le H p)) (inclusion_injective _)

/-- The decisive residual-to-core implication, without an assumed equality
between different definitions of O_{2,p}. -/
theorem O2p_eq_twoCore_of_residual_eq_bot (H : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hX : O2pResidual H p = ⊥) : O2p H p = H.pCoreIn 2 := by
  let D := twoPCore p H
  let P := pCore p (H ⧸ pCore 2 H)
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : D →* P := (q.comp D.subtype).codRestrict P (fun x => x.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pCore 2 H) y.val
    exact ⟨⟨x, by change q x ∈ P; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  have hR : primeToResidual p (O2p H p) = ⊥ :=
    ((primeToResidual p (O2p H p)).map_eq_bot_iff_of_injective
      (O2p H p).subtype_injective).mp hX
  let e : D ≃* O2p H p := D.equivMapOfInjective H.subtype H.subtype_injective
  have hD : primeToResidual p D = ⊥ := by
    apply ((primeToResidual p D).map_eq_bot_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [map_primeToResidual, hR]
  have hP : P = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := H ⧸ pCore 2 H)) ⟨y, hy⟩
    have hyR := mem_primeToResidual_of_pow hn
    have hm := map_primeToResidual_of_surjective p f hf
    rw [hD, Subgroup.map_bot] at hm
    rw [← hm] at hyR
    exact congrArg Subtype.val (mem_bot.mp hyR)
  change (P.comap q).map H.subtype = (pCore 2 H).map H.subtype
  rw [hP]
  change q.ker.map H.subtype = (pCore 2 H).map H.subtype
  rw [QuotientGroup.ker_mk']

/-- The source's Q_H notation, retaining both primality and p > 3. -/
theorem O2p_eq_QH_of_residual_eq_bot (H : Subgroup G) (p : ℕ)
    [Fact p.Prime] (_hp : 3 < p) (hX : O2pResidual H p = ⊥) :
    O2p H p = Chapter13.Section08.Source.QH H :=
  O2p_eq_twoCore_of_residual_eq_bot H p hX

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
