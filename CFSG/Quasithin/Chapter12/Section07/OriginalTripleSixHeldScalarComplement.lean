module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldLocalModel
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarResidual
import Theory.GroupTheory.OddSubgroupLift
import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual scalar-cubic complement in the original Held normalizer

The full original action has two-kernel U and contains the normal scalar
cubic. Lift that cubic through the actual action. Its fixed-free action on
U makes its normalizer disjoint from U, and Frattini gives an internal
complement. The same lift lies in the literal X=O²(O_{2,Z}(K)).
The even/full alternative is retained, without assuming a local splitting.

Source: Aschbacher--Smith12.7.7, printed p.841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes

section Cubic
variable {M B : Type*} [Group M] [Finite M] [Group B] [Finite B]
private theorem cubic_split (f : M →* B) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (q : B) (hq : orderOf q = 3)
    [(zpowers q).Normal]
    (hfix : ∀ c : M, f c = q → ∀ a ∈ f.ker, c * a = a * c → a = 1) :
    ∃ C : Subgroup M, Nat.card C = 3 ∧ C.map f = zpowers q ∧
      f.ker.IsComplement' (normalizer (C : Set M)) := by
  have hqcard : Nat.card (zpowers q) = 3 := by rw [Nat.card_zpowers, hq]
  obtain ⟨C, hC, hinj, hcard, hcover⟩ := f.exists_odd_subgroup_lift hf hker
    (zpowers q) (by rw [hqcard]; decide)
  rw [hqcard] at hcard
  have hd : Disjoint f.ker C := by
    apply disjoint_def.mpr
    intro x hx hxC
    exact congrArg Subtype.val (hinj (a₁ := ⟨x, hxC⟩) (a₂ := 1)
      (show f x = f 1 from (show f x = 1 from hx).trans f.map_one.symm))
  obtain ⟨c, hc, hfc⟩ := (show q ∈ C.map f from hC.symm ▸ mem_zpowers q)
  have hdisj : Disjoint f.ker (normalizer (C : Set M)) := by
    apply disjoint_def.mpr
    intro a ha han
    have hac : a*c*a⁻¹*c⁻¹ ∈ C := C.mul_mem
      ((mem_normalizer_iff.mp han c).mp hc) (C.inv_mem hc)
    have hak : a*c*a⁻¹*c⁻¹ ∈ f.ker := by
      change f (a*c*a⁻¹*c⁻¹) = 1
      simp only [map_mul, map_inv, show f a = 1 from ha, one_mul, inv_one, mul_one,
        mul_inv_cancel]
    have he : a*c*a⁻¹*c⁻¹ = 1 := disjoint_def.mp hd hak hac
    have he' : a*c = c*a := mul_inv_eq_one.mp (by
      simpa only [mul_inv_rev, mul_assoc] using he)
    exact hfix c hfc a ha he'.symm
  let R := (zpowers q).comap f
  change f.ker ⊔ C = R at hcover
  have hCR : C ≤ R := le_sup_right.trans_eq hcover
  have hRcard : Nat.card R = Nat.card f.ker * 3 := by
    rw [← hcover, card_sup_eq_mul_of_normalizes_of_disjoint f.ker C
      (by rw [f.ker.normalizer_eq_top]; exact le_top) hd, hcard]
  let C' := C.subgroupOf R
  have hCcard : Nat.card C' = 3 := (Nat.card_congr (subgroupOfEquivOfLe hCR).toEquiv).trans hcard
  have hi : C'.index = Nat.card f.ker := by
    have hh := C'.card_mul_index
    rw [hCcard, hRcard] at hh
    omega
  have hn : ¬ 3 ∣ C'.index := by
    rw [hi]
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 R := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hCcard)).toSylow hn
  have hs : normalizer (C : Set M) ⊔ f.ker = ⊤ := by
    have hh := P.normalizer_sup_eq_top
    change normalizer ((C.subgroupOf R).map R.subtype : Set M) ⊔ R = ⊤ at hh
    rw [map_subgroupOf_eq_of_le hCR, ← hcover, ← sup_assoc,
      sup_eq_left.mpr (C.le_normalizer.trans le_sup_left)] at hh
    exact hh
  refine ⟨C, hcard, hC, isComplement'_of_card_mul_and_disjoint ?_ hdisj⟩
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint f.ker (normalizer (C : Set M))
    (by rw [f.ker.normalizer_eq_top]; exact le_top) hdisj
  rw [sup_comm, hs, Nat.card_congr Subgroup.topEquiv.toEquiv] at hh
  exact hh.symm

end Cubic

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual order-three scalar subgroup lies in the original scalar
residual, and its full normalizer complements U in the original M. -/
theorem original_tripleSix_held_scalar_complement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let M := normalizer (K : Set G)
    ∃ Y : Subgroup M, Nat.card Y = 3 ∧
      Y.map M.subtype ≤ tripleSixScalarResidual K ∧
      (U.subgroupOf M).IsComplement' (normalizer (Y : Set M)) ∧
      (Nonempty ((normalizer (Y : Set M)) ≃* HexEvenAutomorphisms) ∨
        Nonempty ((normalizer (Y : Set M)) ≃* HexAutomorphisms)) := by
  obtain ⟨f,hker,_,hmark,hact,hquot⟩ := original_tripleSix_held_local_model
    h structural D a t ht heven hB hcenter e
  obtain ⟨_,_,hM,_,_⟩ := original_tripleSix_held_core_recovery
    h structural D a t ht heven hB hcenter e
  let M := normalizer (K : Set G)
  have hUM : U ≤ M := D.le_component.trans K.le_normalizer
  have hcore : pCore 2 M = U.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hUM]
    exact hM
  let f' := f.rangeRestrict
  have hf' : f'.ker = U.subgroupOf M := by
    rw [show f' = f.rangeRestrict from rfl,MonoidHom.ker_rangeRestrict,hker,hcore]
  have hz : hexZ ∈ f.range := by
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm hexEvenZ)
    refine ⟨inclusion K.le_normalizer k,?_⟩
    rw [hmark,hk,a.groupEquiv.apply_symm_apply]
    rfl
  let z : f.range := ⟨hexZ,hz⟩
  have hzorder : orderOf z = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hexZ_order
  have hn : (zpowers z).Normal := by
    have he : zpowers z = (zpowers hexZ).comap f.range.subtype := by
      change zpowers z = (zpowers (f.range.subtype z)).comap f.range.subtype
      rw [← f.range.subtype.map_zpowers z,
        comap_map_eq_self_of_injective f.range.subtype_injective]
    rw [he,←hexCoordinate_kernel]
    infer_instance
  let := hn
  have hfree (c : M) (hc : f' c = z) (u : M) (hu : u ∈ f'.ker)
      (hcu : c*u = u*c) : u = 1 := by
    have huU : (u : G) ∈ U := by
      rwa [hf'] at hu
    let v : U := ⟨u,huU⟩
    have hcz : f c = hexZ := congrArg Subtype.val hc
    have hv := hact c v
    rw [hcz] at hv
    have hcomm : (c : G)*(u : G)*(c : G)⁻¹ = (u : G) := by
      rw [show (c:G)*(u:G) = (u:G)*(c:G) from congrArg Subtype.val hcu,
        mul_inv_cancel_right]
    rw [hcomm] at hv
    have hve : (tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
        (Hexacode.action hexZ (tripleSixPointCoordinates D a v).toAdd)) = v :=
      Subtype.ext hv
    have hv' := congrArg (tripleSixPointCoordinates D a) hve
    rw [MulEquiv.apply_symm_apply] at hv'
    have hscalar := congrArg Multiplicative.toAdd hv'
    have hzv := (Hexacode.scalar_fixed_iff _).mp hscalar
    have hfv : tripleSixPointCoordinates D a v = 1 := hzv
    have hv1 : v = 1 := (tripleSixPointCoordinates D a).injective
      (hfv.trans (map_one _).symm)
    exact Subtype.ext (congrArg (fun x : U => (x : G)) hv1)
  obtain ⟨Y,hY,hYimage,hcomp⟩ := cubic_split f' f.rangeRestrict_surjective
    (by rw [hf']; exact (hcore ▸ pCore_isPGroup)) z hzorder hfree
  have hYfull : Y.map f = zpowers hexZ := by
    have hh := congrArg (Subgroup.map f.range.subtype) hYimage
    rw [map_map,MonoidHom.map_zpowers] at hh
    exact hh
  have hYscalar : Y.map M.subtype ≤ tripleSixScalarResidual K := by
    rintro _ ⟨y,hy,rfl⟩
    have hyz : f y ∈ zpowers hexZ := hYfull ▸ mem_map_of_mem f hy
    have hyEven : f y ∈ hexSign.ker :=
      (zpowers_le.mpr hexSign_Z) hyz
    let v : HexEvenAutomorphisms := ⟨f y,hyEven⟩
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm v)
    have hfyk : f (inclusion K.le_normalizer k) = f y := by
      rw [hmark,hk,a.groupEquiv.apply_symm_apply]
    have hyk : y*(inclusion K.le_normalizer k)⁻¹ ∈ f.ker := by
      change f (y*(inclusion K.le_normalizer k)⁻¹) = 1
      rw [map_mul,map_inv,hfyk,mul_inv_cancel]
    have hykU : ((y*(inclusion K.le_normalizer k)⁻¹ : M) : G) ∈ U := by
      rwa [hker,hcore] at hyk
    have hyK : (y : G) ∈ K := by
      have hh := K.mul_mem (D.le_component hykU) k.property
      simpa only [coe_mul,coe_inv,coe_inclusion,inv_mul_cancel_right] using hh
    let yK : K := ⟨y,hyK⟩
    have hyq : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) yK) = v := by
      apply Subtype.ext
      exact (hmark yK).symm
    have hycenter : v ∈ center HexEvenAutomorphisms := by
      rw [←Hexacode.even_kernel_eq_center,hexEvenCoordinate_kernel]
      obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hyz
      have hh : hexEvenZ ^ n = v := Subtype.ext hn
      exact hh ▸ zpow_mem (mem_zpowers hexEvenZ) n
    have hyZ : yK ∈ centralPreimage (pCore 2 K) := by
      change QuotientGroup.mk' (pCore 2 K) yK ∈ center (K ⧸ pCore 2 K)
      have hh := (centerCongr a.groupEquiv.symm ⟨v,hycenter⟩).property
      change a.groupEquiv.symm v ∈ center (K ⧸ pCore 2 K) at hh
      simpa only [←hyq,a.groupEquiv.symm_apply_apply] using hh
    let yZ : centralPreimage (pCore 2 K) := ⟨yK,hyZ⟩
    have horder : orderOf yZ ∣ 3 := by
      have hh := orderOf_dvd_natCard (⟨y,hy⟩ : Y)
      rw [hY] at hh
      simpa only [yZ,yK,Subgroup.orderOf_mk,Subgroup.orderOf_coe] using hh
    have hyr : yZ ∈ pResidual 2 (centralPreimage (pCore 2 K)) :=
      mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right horder)
    exact mem_map_of_mem K.subtype
      (mem_map_of_mem (centralPreimage (pCore 2 K)).subtype hyr)
  rw [hf'] at hcomp
  refine ⟨Y,hY,hYscalar,hcomp,?_⟩
  have hc : (pCore 2 M).IsComplement' (normalizer (Y : Set M)) := hcore.symm ▸ hcomp
  let eqc := hc.symm.QuotientMulEquiv.symm
  rcases hquot with heven | hfull
  · obtain ⟨eqe⟩ := heven
    exact Or.inl ⟨eqc.trans eqe⟩
  · obtain ⟨eqf⟩ := hfull
    exact Or.inr ⟨eqc.trans eqf⟩

end CFSG.Quasithin.Chapter12.Section07
