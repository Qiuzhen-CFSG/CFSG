module
public import Theory.Representation.BinaryPermutation.FiveBorelFixed
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.SylowCentralizerComplement
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# Borel fixation lifted through the original moved subgroup

A normal subgroup R has alternating-five image in the faithful symmetric-five
action on [U,R]. Its Sylow normalizer fixes the Sylow-fixed vectors there,
by the actual deleted-core quotient and its fixed kernel. Averaging at the
original Sylow subgroup puts each element of Ω₁Z(T) in a coset of [U,R]
with an R-fixed representative. Thus the same Borel fixes Ω₁Z(T), provided
Ω₁Z(T) lies in U. All inclusions, normality and quotient maps are literal.

Source application: Aschbacher–Smith 5.1.13, printed p.637.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- The symmetric-five section makes the normal subgroup’s Borel fix the
original Sylow omega-center when the elementary subgroup contains it. -/
theorem five_borel_fixes_omega
    (T : Sylow 2 G) (U R : Subgroup G) [U.Normal] [R.Normal]
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 (⁅U,R⁆ : Subgroup G)]
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ U)
    (p : G →* Equiv.Perm (Fin 5)) (hp : Function.Surjective p)
    (hk : p.ker = centralizer ((⁅U,R⁆ : Subgroup G) : Set G))
    (him : R.map p = alternatingGroup (Fin 5))
    (f : Additive (⁅U,R⁆ : Subgroup G) →ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (hs : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation ⁅U,R⁆ p hp hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (f v))
    (hf : f.ker = fixedSpace (NormalElementaryQuotient.representation ⁅U,R⁆ p hp hk)
      (R.map p)) :
    (normalizer ((T : Subgroup G).subgroupOf R : Set R)).map
      R.subtype ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let V := ⁅U,R⁆
  let r := NormalElementaryQuotient.representation V p hp hk
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal R
  have hPm : (P : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R := by
    rw [hP,subgroupOf_map_subtype]
  let q : R →* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr him).toMonoidHom.comp (p.subgroupMap R)
  have hq : Function.Surjective q :=
    (MulEquiv.subgroupCongr him).surjective.comp (p.subgroupMap_surjective R)
  let Q := P.mapSurjective hq
  have hkernel : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5), r g v = v := by
    intro v hv g hg
    have hh : v ∈ fixedSpace r (alternatingGroup (Fin 5)) := by
      rw [←him,←hf]
      exact hv
    exact hh ⟨g,hg⟩
  rintro _ ⟨a,ha,rfl⟩ z hz
  have haP : a ∈ normalizer (P : Set R) := by
    change a ∈ normalizer ((P : Subgroup R) : Set R)
    rwa [hP]
  have haQ : q a ∈ normalizer (Q : Set (alternatingGroup (Fin 5))) :=
    (le_normalizer_map q) (mem_map_of_mem q haP)
  have hzT := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzC : z ∈ centralizer ((P : Subgroup R).map R.subtype : Set G) := by
    intro x hx
    exact hzT.2.2 x (show x ∈ (T : Subgroup G) ⊓ R from hPm ▸ hx).1
  have hRV : R ≤ normalizer (V : Set G) := normalizer_commutator_ge_right U R
  obtain ⟨u,hu,huz⟩ := fixed_coset_of_sylow R V hRV
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) P z
    (fun a ha => by
      change ⁅a,z⁆ ∈ ⁅U,R⁆
      rw [commutator_comm U R]
      exact commutator_mem_commutator ha (hZ hz))
    (fun a ha => hzC a (mem_map_of_mem R.subtype ha))
  have huC : u ∈ centralizer ((P : Subgroup R).map R.subtype : Set G) := by
    have hh := (centralizer ((P : Subgroup R).map R.subtype : Set G)).mul_mem
      (centralizer_le (map_subtype_le _) huz)
      ((centralizer ((P : Subgroup R).map R.subtype : Set G)).inv_mem hzC)
    simpa only [mul_inv_cancel_right] using hh
  let v : Additive V := Additive.ofMul ⟨u,hu⟩
  have hv : ∀ g ∈ Q, r g.val v = v := by
    rintro g ⟨b,hb,rfl⟩
    change r (p b.val) v = v
    exact ((NormalElementaryQuotient.mem_fixedSpace_image V p hp hk
      ((P : Subgroup R).map R.subtype) v).mpr huC) ⟨p b.val,
        mem_map_of_mem p (mem_map_of_mem R.subtype hb)⟩
  have hfix := BinaryPermutation.FiveBorelFixed.normalizer_fixes_lift r f hs he hkernel Q (q a) haQ v hv
  have hau : a.val * u * a.val⁻¹ = u := by
    have hh := congrArg (fun w : Additive V => (w.toMul : G)) hfix
    change ((r (p a.val) v).toMul : G) = u at hh
    rwa [NormalElementaryQuotient.representation_apply] at hh
  have huc : u ∈ centralizer ({a.val} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hau).symm
  have huzc : u * z ∈ centralizer ({a.val} : Set G) :=
    mem_centralizer_singleton_iff.mpr (huz a.val a.property).symm
  have hzc := (centralizer ({a.val} : Set G)).mul_mem
    ((centralizer ({a.val} : Set G)).inv_mem huc) huzc
  have hzz : z ∈ centralizer ({a.val} : Set G) := by
    simpa only [inv_mul_cancel_left] using hzc
  exact mem_centralizer_singleton_iff.mp hzz

end Theory.GroupTheory
