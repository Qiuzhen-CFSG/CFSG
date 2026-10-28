module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.AmbientKernel
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SwappingNormalizer
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.FixedCubic
public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.NormalizerProduct.InnerCorrection
public import Theory.GroupTheory.CentralThreeInvertedPlane

/-!
# The remaining block centralizer in the swapping branch

If C_G(L)=1, the ambient kernel calculation gives C_G(U)=Z(U). A nontrivial
cubic in the residual quotient centralizes the selected swap. Inner correction
in U makes its action on U commute with that swap. Taking an appropriate
fourth power gives an actual cubic with the same quotient image. Its commutator
with the swap lies in Z(U), so the coprime central-kernel lifting theorem
forces it to commute with the swap itself. It therefore normalizes the
literal A=⟨s,[U,s]⟩, contrary to the checked N_H(A)=T.

Thus the remaining swapping branch has a nontrivial elementary D=C_G(L),
with N_G(D)=N_G(L), H not normalizing D, C_G(U)=Z(U)D and O₂(H)=UD.
The final consumer applies this to the original source alternative.
The remaining nontrivial-kernel fusion exclusion belongs to
qt-d-14414-g2-source, as does the subsequent application of independent
I.4.5 recognition from qt-i45-g2-recognition. This is not yet the full
14.4.3–5 source theorem. Earlier source inputs retain their existing owners;
final 14.4.14 assembly belongs to qt-d-14414-source.

Source: Aschbacher–Smith, proof of 14.4.4(6), printed p.1007.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
      q.right.map F.U.subtype)
include d earlier hq chosen previous hne hZ hcard g hgL hgP hgH q hsX hs hout hswap

/-- Swapping with trivial block centralizer contradicts the literal relative normalizer. -/
theorem source_block_centralizer_ne_bot_of_swapping : centralizer (L : Set G) ≠ ⊥ := by
  intro hD
  let := chosen.elementary
  have hC : centralizer (F.U : Set G) = F.ZU := by
    rw [source_core_centralizer_eq_center_join d earlier hq chosen previous F hne hZ hcard,
      hD,sup_bot_eq]
  let f := F.uAction
  let π := QuotientGroup.mk' (pCore 2 F.H)
  have hk : ((quotientAut (center F.U)).comp f).ker = pCore 2 F.H :=
    source_uhat_kernel d earlier hq chosen previous F hZ
  have hswap' : q.left.map (f s).toMonoidHom = q.right := by
    apply map_injective F.U.subtype_injective
    rw [map_map] at hswap ⊢
    exact hswap
  obtain ⟨k,hkK,hkn,hk3,hks⟩ := q.fixed_cubic_in_residual_quotient_of_swap f (pCore 2 F.H)
    hk (source_residual_nine d earlier hq chosen previous F hne hZ hcard).2 s hs hswap'
  let α := f s
  let β := f k * α * (f k)⁻¹
  have hα : α ^ 2 = 1 := by dsimp [α]; rw [←map_pow,hs,map_one]
  have hβ : β ^ 2 = 1 := by
    change (MulAut.conj (f k) α) ^ 2 = 1
    rw [←map_pow,hα,map_one]
  have hquot : quotientAut (center F.U) β = quotientAut (center F.U) α := by
    let σ := (quotientAut (center F.U)).comp f
    have he : σ (k*s*k⁻¹) = σ s := by
      rw [σ.eq_iff, hk]
      have hp : π (k*s*k⁻¹) = π s := by
        rw [map_mul,map_mul,map_inv,hks.symm.eq,mul_inv_cancel_right]
      rw [π.eq_iff,QuotientGroup.ker_mk'] at hp
      exact hp
    simpa only [σ,β,α,MonoidHom.comp_apply,map_mul,map_inv] using he
  obtain ⟨v,hv⟩ := q.swap_inner_correction α β hα hβ hswap' hquot
  let vH : F.H := ⟨v,F.U_le_H v.property⟩
  let b := vH*k
  have hvQ : vH ∈ pCore 2 F.H := by
    have hm := source_closure_le_twoCore d earlier hq chosen previous.structural
      previous.alternatives F hne v.property
    obtain ⟨w,hw,he⟩ := hm
    exact (Subtype.ext he : w=vH) ▸ hw
  have hbπ : π b = π k := by
    dsimp [b]
    rw [map_mul,show π vH=1 from (QuotientGroup.eq_one_iff _).mpr hvQ,one_mul]
  have hbcomm : Commute (f b) α := by
    apply mul_inv_eq_iff_eq_mul.mp
    have hfv : f vH = MulAut.conj v := MulEquiv.ext (fun _ => rfl)
    dsimp [b]
    rw [map_mul,hfv]
    calc
      _ = MulAut.conj v * β * (MulAut.conj v)⁻¹ := by dsimp [β]; group
      _ = α := hv
  have hb3 : b ^ 3 ∈ pCore 2 F.H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (b^3)=1
    rw [map_pow,hbπ]
    exact hk3
  obtain ⟨n,hn⟩ := pCore_isPGroup.exists_pow_pow_eq_one (⟨b^3,hb3⟩ : pCore 2 F.H)
  have hn' : (b^3)^(2^n)=1 := congrArg Subtype.val hn
  let c := b^(4^n)
  have hc3 : c^3=1 := by
    calc
      c^3=((b^3)^(2^n))^(2^n) := by
        simp only [c,←pow_mul]
        congr 1
        rw [show 4=2*2 from rfl,mul_pow]
        ring
      _=1 := by rw [hn',one_pow]
  have hcπ : π c = π k := by
    rw [map_pow,hbπ]
    have hp : (π k)^4=π k := by rw [show 4=3+1 from rfl,pow_succ,hk3,one_mul]
    have hpower (m : ℕ) : (π k)^(4^m)=π k := by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ,pow_mul,ih,hp]
    exact hpower n
  have hfQ : f.ker ≤ pCore 2 F.H := by
    intro x hx
    rw [←hk]
    change quotientAut (center F.U) (f x)=1
    rw [show f x=1 from hx,map_one]
  have hfC : f.ker ≤ center F.H := by
    intro x hx
    have hxC : (x : G) ∈ centralizer (F.U : Set G) := by
      intro v hv
      have he := congrArg Subtype.val (DFunLike.congr_fun hx (⟨v,hv⟩ : F.U))
      change (x : G)*v*(x : G)⁻¹=v at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hxZ : (x : G) ∈ F.ZU := hC ▸ hxC
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact ((point_centralizer F hZ).le y.property x hxZ).symm
  have hcs : Commute c s := f.commute_of_map_commute_of_coprime_torsion hfC
    (pCore_isPGroup.to_le hfQ) (by decide : Nat.Coprime 2 3) c s hc3 (by
      change Commute (f (b^(4^n))) α
      rw [map_pow]
      exact hbcomm.pow_left _)
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  have hcN : (c : G) ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆).map
      (MulAut.conj (c : G)).toMonoidHom = _
    have hUmap : F.U.map (MulAut.conj (c : G)).toMonoidHom = F.U :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V F.H c.property)
    rw [Subgroup.map_sup,map_commutator,MonoidHom.map_zpowers,hUmap]
    have he : MulAut.conj (c : G) (s : G) = s := by
      change (c : G)*(s : G)*(c : G)⁻¹=s
      have heq : (c : G)*(s : G)=(s : G)*(c : G) := congrArg Subtype.val hcs.eq
      rw [heq,mul_inv_cancel_right]
    change zpowers (MulAut.conj (c : G) (s : G)) ⊔
      ⁅F.U,zpowers (MulAut.conj (c : G) (s : G))⁆ = A
    rw [he]
  have hcT : (c : G) ∈ (T : Subgroup G) :=
    (source_swapping_normalizer_eq_sylow d earlier hq chosen previous F hne hZ hcard
      g hgL hgP hgH q s hsX hs hout hswap) ▸ ⟨c.property,hcN⟩
  have hc1 : c=1 := by
    have ho := T.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 2 3)
      (⟨c,hcT⟩ : T)
    have hd : orderOf (⟨c,hcT⟩ : T) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (show (⟨c,hcT⟩ : T)^3=1 from
        Subtype.ext (congrArg (fun x : F.H => (x : G)) hc3))
    exact Subtype.ext (congrArg (fun x : T => (x : G))
      (show (⟨c,hcT⟩ : T)=1 from orderOf_eq_one_iff.mp (ho.eq_one_of_dvd hd)))
  exact hkn (hcπ.symm.trans (by rw [hc1,map_one]))
end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source configuration is constructed unless the swapping branch has
an elementary nontrivial block centralizer with its exact ambient normalizer.
The final source owner must still exclude this remaining kernel geometry. -/
theorem source_configuration_or_nontrivial_block_centralizer
    (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) ∨
      (let D := centralizer (L : Set G)
       D ≠ ⊥ ∧ IsElementaryAbelian 2 D ∧
       normalizer (D : Set G) = normalizer (L : Set G) ∧
       ¬ F.H ≤ normalizer (D : Set G) ∧
       centralizer (F.U : Set G) = F.ZU ⊔ D ∧
       F.H.pCoreIn 2 = F.U ⊔ D ∧ Disjoint F.U D ∧
       Nat.card (centralizer (F.U : Set G)) = 2 * Nat.card D ∧
       Nat.card (F.H.pCoreIn 2) = 32 * Nat.card D) := by
  rcases source_configuration_or_swapping d earlier hq chosen previous F hne hZ hcard with
    hconfig | ⟨q,g,s,hgL,hgP,hgH,hsX,hs,hout,_hTL,hswap,_hD,_hA,_hAc⟩
  · exact Or.inl hconfig
  · have hD := source_block_centralizer_ne_bot_of_swapping d earlier hq chosen previous
      F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap
    have hN := source_block_centralizer_normalizer_of_ne_bot d earlier hq chosen previous
      F hne hZ hcard hD
    refine Or.inr ⟨hD,source_block_centralizer_elementary d earlier hq chosen previous
      F hne hZ hcard,hN,?_,
      source_core_centralizer_eq_center_join d earlier hq chosen previous F hne hZ hcard,
      source_twoCore_eq_closure_join_block_centralizer d earlier hq chosen previous F hne hZ hcard,
      source_block_centralizer_disjoint_closure d earlier hq chosen previous F hne hZ hcard,
      source_extra_kernel_card d earlier hq chosen previous F hne hZ hcard⟩
    rw [hN]
    exact (higherRankHypothesis d earlier hq chosen).flag_escape F previous.alternatives
end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
