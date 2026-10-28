module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicProjective
public import Theory.GroupTheory.CentralExtensionAbelianSylowSection
public import Theory.GroupTheory.QuotientKernelComplement
public import Mathlib.GroupTheory.SchurZassenhaus
public import Theory.GroupTheory.PGroup.OrderTwentySevenMarkedCenter
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCosetFusion

/-!
# Splitting the same cubic normalizer from the source nonfusion claim

Baumeister's last paragraph of Lemma 2.4 distinguishes an independent cubic
σ from sσ inside C_G(s). If its Sylow three-subgroup were nonabelian, its
order would be 27 and its center would be the original ⟨s⟩. Extraspecial
coset fusion would then conjugate σ to sσ, a contradiction.

An abelian Sylow subgroup splits the central extension C_G(s) → A₆ by
transfer: the derived subgroup is a complement to the same cubic. Its image
is normal in N_G(⟨s⟩). Quotienting by this image leaves a group of order six;
Schur–Zassenhaus and inverse image give a complement to the ORIGINAL cubic
kernel in the FULL normalizer. The final theorem identifies this complement
with PGL₂(9) through the literal original quotient map.

The nonfusion claim remains explicit. This module does not construct its
plane-complement witness σ, the second/third parabolics, or OriginalMarking.
Those are still source obligations of the ambient construction. No split
A₅ complement in an H-type involution centralizer is assumed.

Source: B. Baumeister, *A geometry for groups of J₃-type*, Archiv der
Mathematik 88 (2007), Lemma 2.4, printed pp.495–496.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- Transfer splits the cubic centralizer along its canonical derived subgroup. -/
theorem centralizer_derived_complement (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (S : Sylow 3 (centralizer ({s} : Set G))) (hS : IsMulCommutative S) :
    (cubicKernel s).IsComplement' (_root_.commutator (centralizer ({s} : Set G))) := by
  let C := centralizer ({s} : Set G)
  let q := QuotientGroup.mk' (cubicKernel s)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (C ⧸ cubicKernel s) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hp : IsPGroup 3 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 1) (by simpa using cubicKernel_card s hs)
  let P : Sylow 3 (C ⧸ cubicKernel s) := Sylow.nonempty.some
  let R := P.comapOfKerIsPGroup q hp (by rw [q.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]; exact le_top)
  have hR : IsMulCommutative ((P : Subgroup (C ⧸ cubicKernel s)).comap q) := by
    change IsMulCommutative R
    let _ := hS
    let a := S.equiv R
    refine ⟨⟨fun x y => a.symm.injective ?_⟩⟩
    exact (a.symm.map_mul x y).trans ((mul_comm (a.symm x) (a.symm y)).trans
      (a.symm.map_mul y x).symm)
  obtain ⟨t,ht,htD⟩ := CentralExtension.exists_derived_section_of_abelian_sylow_preimage
    q (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact cubicKernel_central s)
    hp P hR
  have htq (x) : q (t x) = x := DFunLike.congr_fun ht x
  have hc : t.range.IsComplement' (cubicKernel s) :=
    isComplement_range_left htq
  rw [htD] at hc
  exact hc.symm

/-- Extend the derived complement to a complement in the same full normalizer. -/
theorem normalizer_kernel_complement_of_abelian_sylow {z : G}
    (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (S : Sylow 3 (centralizer ({s} : Set G))) (hS : IsMulCommutative S) :
    ∃ M : Subgroup (normalizer (zpowers s : Set G)),
      (cubicNormalizerKernel s).IsComplement' M := by
  let C := centralizer ({s} : Set G)
  let N := normalizer (zpowers s : Set G)
  let C' := C.subgroupOf N
  let i : C →* N := inclusion (cubic_centralizer_le_normalizer s)
  have hi : Function.Injective i := inclusion_injective _
  have hiR : i.range = C' := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
  have hidx : C'.index = 2 := by
    have hh := C'.index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (cubic_centralizer_le_normalizer s)).toEquiv,
      cubic_centralizer_card s hs e, cubic_normalizer_card h hc s hs e] at hh
    omega
  have hC' : C'.Normal := normal_of_index_eq_two hidx
  let _ := hC'
  let D := (_root_.commutator C).map i
  have hD : D = ⁅C',C'⁆ := by dsimp only [D]; rw [map_commutator_eq, hiR]
  have hDn : D.Normal := by rw [hD]; infer_instance
  let _ := hDn
  have hsplit := centralizer_derived_complement s hs e S hS
  have hDcard : Nat.card D = 360 := by
    dsimp only [D]
    rw [card_map_of_injective hi,
      ← Nat.card_congr hsplit.symm.QuotientMulEquiv.toEquiv, Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup]
    norm_num
  have hdis : Disjoint (cubicNormalizerKernel s) D := by
    apply disjoint_def.mpr
    intro x hxK hxD
    obtain ⟨y,hy,rfl⟩ := hxD
    have hy1 : y = 1 := hsplit.disjoint.le_bot ⟨hxK,hy⟩
    exact congrArg i hy1
  let q := QuotientGroup.mk' D
  let K := (cubicNormalizerKernel s).map q
  have hK : K.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective D)
  let _ := hK
  have hqinj : Function.Injective (q.subgroupMap (cubicNormalizerKernel s)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxD : (x : N) ∈ D := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    exact Subtype.ext (hdis.le_bot ⟨x.property,hxD⟩)
  have hKcard : Nat.card K = 3 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap (cubicNormalizerKernel s))
      ⟨hqinj,q.subgroupMap_surjective _⟩).toEquiv]
    exact cubicNormalizerKernel_card s hs
  have hQcard : Nat.card (N ⧸ D) = 6 := by
    have hh := D.index_mul_card
    rw [hDcard, cubic_normalizer_card h hc s hs e] at hh
    change Nat.card (N ⧸ D) * 360 = 2160 at hh
    omega
  have hKindex : K.index = 2 := by
    have hh := K.index_mul_card
    rw [hKcard,hQcard] at hh
    omega
  obtain ⟨U,hU⟩ := exists_right_complement'_of_coprime (show Nat.Coprime (Nat.card K) K.index by
    rw [hKcard,hKindex]; decide)
  exact ⟨U.comap q, QuotientKernelComplement.complement_comap q (cubicNormalizerKernel s) U
    (by simpa only [q, QuotientGroup.ker_mk'] using hdis) hU⟩

/-- The literal nonfusion comparison in Baumeister 2.4 excludes a nonabelian Sylow of order 27. -/
theorem abelian_sylow_of_cubic_nonfusion
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (σ : centralizer ({s} : Set G)) (hσ : orderOf σ = 3)
    (hσout : σ ∉ cubicKernel s) (hn : ¬ IsConj (σ : G) (s * (σ : G))) :
    ∃ S : Sylow 3 (centralizer ({s} : Set G)), IsMulCommutative S := by
  let C := centralizer ({s} : Set G)
  have hp : IsPGroup 3 (zpowers σ) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hσ]; rfl)
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  refine ⟨S,?_⟩
  by_contra hnS
  have hScard : Nat.card S = 27 := by
    rw [S.card_eq_multiplicity, cubic_centralizer_card s hs e]
    decide +kernel
  let _ : IsExtraspecial 3 (S : Subgroup C) := OrderTwentySeven.extraspecial hScard hnS
  have hKp : IsPGroup 3 (cubicKernel s) := IsPGroup.of_card (n := 1) (by
    simpa using cubicKernel_card s hs)
  have hKS : cubicKernel s ≤ (S : Subgroup C) := hKp.le_sylow_of_normal S
  let K := (cubicKernel s).subgroupOf (S : Subgroup C)
  have hKcard : Nat.card K = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv).trans (cubicKernel_card s hs)
  have hKZ : K ≤ center (S : Subgroup C) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (cubicKernel_central s hx) y)
  have hKeq : K = center (S : Subgroup C) := eq_of_le_of_card_ge hKZ (by
    rw [hKcard, OrderTwentySeven.center_card hScard hnS])
  let σS : (S : Subgroup C) := ⟨σ,hS (mem_zpowers σ)⟩
  let sC : C := ⟨s,mem_centralizer_singleton_iff.mpr rfl⟩
  have hsK : sC ∈ cubicKernel s := mem_zpowers s
  let sS : (S : Subgroup C) := ⟨sC,hKS hsK⟩
  have hsZ : sS ∈ center (S : Subgroup C) := hKZ hsK
  have hσZ : σS ∉ center (S : Subgroup C) := by
    rw [← hKeq]
    exact hσout
  have hzq : QuotientGroup.mk' (center (S : Subgroup C)) sS = 1 := (QuotientGroup.eq_one_iff sS).mpr hsZ
  have hf : IsConj σS (sS * σS) :=
    IsExtraspecial.isConj_of_center_quotient_eq_prime (p := 3) hσZ (by
      rw [map_mul, hzq, one_mul])
  exact hn ((C.subtype.comp (S : Subgroup C).subtype).map_isConj hf)

/-- The source nonfusion claim suffices to split over the original cubic kernel. -/
theorem normalizer_kernel_complement_of_cubic_nonfusion {z : G}
    (h : HTypeAt z) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (σ : centralizer ({s} : Set G)) (hσ : orderOf σ = 3)
    (hσout : σ ∉ cubicKernel s) (hn : ¬ IsConj (σ : G) (s * (σ : G))) :
    ∃ M : Subgroup (normalizer (zpowers s : Set G)),
      (cubicNormalizerKernel s).IsComplement' M := by
  obtain ⟨S,hS⟩ := abelian_sylow_of_cubic_nonfusion s hs e σ hσ hσout hn
  exact normalizer_kernel_complement_of_abelian_sylow h hc s hs e S hS

/-- The resulting PGL₂(9) marking agrees pointwise with the original quotient projection. -/
theorem normalizer_complement_projective_of_cubic_nonfusion {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (s : G) (hs : orderOf s = 3)
    (e : (centralizer ({s} : Set G) ⧸ cubicKernel s) ≃* alternatingGroup (Fin 6))
    (σ : centralizer ({s} : Set G)) (hσ : orderOf σ = 3)
    (hσout : σ ∉ cubicKernel s) (hn : ¬ IsConj (σ : G) (s * (σ : G))) :
    ∃ (M : Subgroup (normalizer (zpowers s : Set G)))
      (eQ : (normalizer (zpowers s : Set G) ⧸ cubicNormalizerKernel s) ≃*
        GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
      (eM : M ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F),
      (cubicNormalizerKernel s).IsComplement' M ∧
      ∀ x : M, eM x = eQ (QuotientGroup.mk' (cubicNormalizerKernel s) x.val) := by
  obtain ⟨M,hM⟩ := normalizer_kernel_complement_of_cubic_nonfusion D.localType hc s hs e σ hσ hσout hn
  obtain ⟨eQ⟩ := cubic_normalizer_quotient_pgl_nine P hc s hs e
  exact ⟨M,eQ,hM.symm.QuotientMulEquiv.symm.trans eQ,hM,fun _ => rfl⟩

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
