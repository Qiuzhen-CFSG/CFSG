module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Action
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction
public import CFSG.Quasithin.Chapter3.Section02.SourceXiSigns
public import BenderSuzuki.External.Huppert.IV.ResidualCommutator
public import Theory.GroupTheory.PGroup.FrattiniActionImage

/-!
# The original Xi module kernels

Write J=XT and V=[R₂(J),X]. The two-perfect commutator identity gives
[V,X]=V. For nontrivial V, irreducibility on the original Frattini quotient
forces C_X(V) into its Frattini preimage: a full image would make X fix V.

The Sylow centralizer then acts trivially on that Frattini quotient. Its
image on X/O₂(X) is both a two-group and an odd-prime group by Burnside's
Frattini kernel theorem, hence trivial. A.4.2 identifies O₂(J) as a maximal
signalizer in the actual section centralizer and proves C_T(V)=O₂(J).

The kernel statements need only the original Xi membership and V≠1. Their
ratio consumer retains the genuine earlier A/C and 15.4.2(4) inputs. The
source nontriviality witness and final Xi-minus assembly remain independent.
Source: Aschbacher--Smith, Lemma 3.2.13, printed pp.584--585; A.4.2(4--5), p.57.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
variable {G : Type*} [Group G] [Finite G] {T X : Subgroup G}

/-- The original two-perfect X acts idempotently on [R₂(XT),X]. -/
theorem sourceModule_commutator_self (hX : X ∈ Chapter1.Xi G T) :
    ⁅sourceModule T X, X.subgroupOf (sourceGroup T X)⁆ = sourceModule T X := by
  let J := sourceGroup T X
  let Y := X.subgroupOf J
  have hY : IsPPerfect 2 Y := hX.perfect.of_surjective
    (subgroupOfEquivOfLe (show X ≤ J from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show X ≤ J from le_sup_left)).symm.surjective
  have hres : BenderSuzuki.External.hktPResidual 2 Y = ⊤ :=
    hY _ BenderSuzuki.External.hktPResidual_normal
      BenderSuzuki.External.hktPResidual_quotient_isPGroup
  have hmap : (BenderSuzuki.External.hktPResidual 2 Y).map Y.subtype = Y := by
    rw [hres, ← MonoidHom.range_eq_map, range_subtype]
  let W := reducedTwoSubgroup J
  let := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
  have he := BenderSuzuki.External.commutator_map_pResidual_idempotent_of_isPGroup
    2 W Y (IsElementaryAbelian.isPGroup 2 W)
    (by rw [normalizer_eq_top]; exact le_top)
  dsimp only at he
  rw [hmap] at he
  exact he

/-- T-irreducibility puts the original X-kernel in the literal Frattini preimage. -/
theorem source_kernel_le_frattini (hX : X ∈ Chapter1.Xi G T)
    (hne : sourceModule T X ≠ ⊥) :
    (centralizer (sourceModule T X : Set (sourceGroup T X))).comap
      (inclusion (show X ≤ sourceGroup T X from le_sup_left)) ≤
      (frattini (Chapter1.XiQuotient X)).comap (QuotientGroup.mk' (pCore 2 X)) := by
  let J := sourceGroup T X
  let V := sourceModule T X
  let := sourceModule_normal hX
  let C := centralizer (V : Set J)
  let i : X →* J := inclusion (show X ≤ J from le_sup_left)
  let K := C.comap i
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (Chapter1.XiQuotient X))
  let f := r.comp q
  let := conjMulDistribMulActionOfLeNormalizer T X hX.invariant
  have hK : ∀ t : T, ∀ x ∈ K, (t • x : X) ∈ K := by
    intro t x hx
    exact (inferInstance : C.Normal).conj_mem (i x) hx
      (⟨t, (show T ≤ J from le_sup_right) t.property⟩ : J)
  have hstable : ∀ t : T, ∀ y ∈ K.map f,
      Chapter1.xiFrattiniAction T X hX.invariant t y ∈ K.map f := by
    rintro t y ⟨x, hx, rfl⟩
    refine ⟨t • x, hK t x hx, ?_⟩
    simp only [f, r, q, Chapter1.xiFrattiniAction, MonoidHom.comp_apply,
      quotientAut_apply_mk]
    rfl
  rcases hX.irreducible (K.map f) hstable with hb | ht
  · intro x hx
    change q x ∈ frattini (Chapter1.XiQuotient X)
    apply (QuotientGroup.eq_one_iff (q x)).mp
    exact (show f x = 1 from mem_bot.mp (hb ▸ mem_map_of_mem f hx))
  · have hqK : K.map q = ⊤ := by
      apply frattini_nongenerating
      have hh := congrArg (Subgroup.comap r) ht
      rw [← Subgroup.map_map] at hh
      simpa only [comap_map_eq, r, QuotientGroup.ker_mk', comap_top] using hh
    have hcore : pCore 2 X ≤ K := by
      intro x hx
      have h := source_twoCore_le_action_kernel hX hx
      exact (QuotientGroup.eq_one_iff (i x)).mp
        (show QuotientGroup.mk' C (i x) = 1 from h)
    have hKtop : K = ⊤ := by
      have hh := congrArg (Subgroup.comap q) hqK
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top,
        sup_of_le_left hcore] using hh
    have hXC : X.subgroupOf J ≤ C := by
      intro x hx
      exact (show (⟨x.val, hx⟩ : X) ∈ K from hKtop.symm ▸ mem_top _)
    have he : ⁅V, X.subgroupOf J⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hXC)
    exact (hne ((sourceModule_commutator_self hX).symm.trans he)).elim

/-- The X-kernel containment alone identifies the original Sylow centralizer. -/
theorem source_sylow_centralizer_eq_core_of_kernel (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (hker : (centralizer (sourceModule (T : Subgroup G) X :
      Set (sourceGroup (T : Subgroup G) X))).comap
        (inclusion (show X ≤ sourceGroup (T : Subgroup G) X from le_sup_left)) ≤
      (frattini (Chapter1.XiQuotient X)).comap (QuotientGroup.mk' (pCore 2 X))) :
    (T : Subgroup G).subgroupOf (sourceGroup (T : Subgroup G) X) ⊓
      centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
        pCore 2 (sourceGroup (T : Subgroup G) X) := by
  let J := sourceGroup (T : Subgroup G) X
  let V := sourceModule (T : Subgroup G) X
  let := sourceModule_normal hX
  let C := centralizer (V : Set J)
  let i : X →* J := inclusion (show X ≤ J from le_sup_left)
  let S := (T : Subgroup G).subgroupOf J ⊓ C
  let N := normalizer (X : Set G)
  let tmap : S →* (T : Subgroup G) :=
    { toFun := fun s => ⟨s.val.val, s.property.1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let nmap : S →* N := (inclusion hX.invariant).comp tmap
  let aX : S →* MulAut X := X.normalizerMonoidHom.comp nmap
  let a := (Chapter3.xiQuotientNormalizerAction X).comp nmap
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := QuotientGroup.mk' (frattini (Chapter1.XiQuotient X))
  have hfix : (quotientAut (frattini (Chapter1.XiQuotient X))).comp a = 1 := by
    apply MonoidHom.ext
    intro s
    apply MulEquiv.ext
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (frattini (Chapter1.XiQuotient X)) y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) v
    have hc : ⁅s.val, i x⁆ ∈ C :=
      (commutator_le_left C ⊤) (commutator_mem_commutator s.property.2 (mem_top _))
    have hk : aX s x * x⁻¹ ∈ C.comap i := hc
    have hf := hker hk
    have hq : r (q (aX s x * x⁻¹)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hf
    rw [map_mul, map_inv, map_mul, map_inv] at hq
    change quotientAut (frattini (Chapter1.XiQuotient X))
      (quotientAut (pCore 2 X) (aX s)) (r (q x)) = r (q x)
    rw [quotientAut_apply_mk, quotientAut_apply_mk]
    exact mul_inv_eq_one.mp hq
  obtain ⟨p, hp, ho, hodd⟩ := hX.odd_quotient
  let : Fact p.Prime := ⟨hp⟩
  have hSp : IsPGroup 2 S :=
    (T.isPGroup'.comap_subtype : IsPGroup 2 ((T : Subgroup G).subgroupOf J)).to_le inf_le_left
  have hap : IsPGroup p a.range :=
    MonoidHom.isPGroup_range_of_frattini_range hodd.isPGroup a
      (by rw [hfix]; exact IsPGroup.of_card (n := 0) (by simp))
  have ha2 : IsPGroup 2 a.range :=
    hSp.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  have hd : Disjoint a.range a.range :=
    IsPGroup.disjoint_of_ne 2 p (by intro e; rw [← e] at ho; norm_num at ho)
      _ _ ha2 hap
  have ha : a = 1 := MonoidHom.range_eq_bot_iff.mp (disjoint_self.mp hd)
  let CS := ChapterA.Section04.twoSectionCentralizer X N
  let Sg := S.map J.subtype
  have hSC : Sg ≤ CS := by
    rintro g ⟨s, hs, rfl⟩
    refine ⟨hX.invariant hs.1, hX.invariant hs.1, ?_⟩
    intro x hx
    let u : X := ⟨x, hx⟩
    have hh := DFunLike.congr_fun (DFunLike.congr_fun ha (⟨s, hs⟩ : S)) (q u)
    change quotientAut (pCore 2 X) (aX ⟨s, hs⟩) (q u) = q u at hh
    rw [quotientAut_apply_mk] at hh
    have hq : q (aX ⟨s, hs⟩ u * u⁻¹) = 1 := by
      rw [map_mul, map_inv, hh, mul_inv_cancel]
    have hk : aX ⟨s, hs⟩ u * u⁻¹ ∈ pCore 2 X :=
      (QuotientGroup.eq_one_iff _).mp hq
    exact mem_map_of_mem X.subtype hk
  have hcoreS : pCore 2 J ≤ S := by
    apply le_inf
    · exact pCore_isPGroup.le_sylow_of_normal
        (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    · exact sourceModule_core_centralizes (T : Subgroup G) X
  obtain ⟨P, hP⟩ := ChapterA.Section04.sylow_core_sectionCentralizer T X hX.perfect hX.invariant
  have hRle : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ Sg := map_mono hcoreS
  have hPS : (P : Subgroup CS) ≤ Sg.subgroupOf CS := by
    intro x hx
    exact hRle (hP ▸ mem_map_of_mem CS.subtype hx)
  have he : Sg.subgroupOf CS = (P : Subgroup CS) :=
    P.is_maximal' (hSp.map J.subtype).comap_subtype hPS
  have hSle : Sg ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
    intro s hs
    have hp : (⟨s, hSC hs⟩ : CS) ∈ (P : Subgroup CS) := by
      have ht : (⟨s, hSC hs⟩ : CS) ∈ Sg.subgroupOf CS := hs
      simpa only [he] using ht
    rw [← hP]
    exact ⟨⟨s, hSC hs⟩, hp, rfl⟩
  apply map_injective J.subtype_injective
  exact le_antisymm hSle hRle

/-- Nontriviality of the original commutator module discharges both kernel steps. -/
theorem source_sylow_centralizer_eq_core (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (hne : sourceModule (T : Subgroup G) X ≠ ⊥) :
    (T : Subgroup G).subgroupOf (sourceGroup (T : Subgroup G) X) ⊓
      centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
        pCore 2 (sourceGroup (T : Subgroup G) X) :=
  source_sylow_centralizer_eq_core_of_kernel T hX (source_kernel_le_frattini hX hne)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
