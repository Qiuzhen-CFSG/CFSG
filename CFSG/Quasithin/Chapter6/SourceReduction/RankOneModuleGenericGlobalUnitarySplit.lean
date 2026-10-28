module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryMoved
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeLargeField
public import Theory.Representation.SL3.DualFirstCohomology
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.FirstCohomologyDuality
public import Theory.GroupTheory.DoubleCoverCentralizer.ProjectiveRadicalSplitting.QuotientAction
public import Theory.Representation.IrreducibleFixedPoints

/-!
# The full moved core in the proper unitary branch

For R = O₂(J) and N = K ∩ R, the faithful simple section on R/Φ(R) has
binary dimension 3m, whereas the whole space has dimension at most 3m+1.
The remaining dimension is trivial. Natural and dual SL₃(2^m) first
cohomology vanish for m > 1, so both possible extensions split. Thus the
literal displacement space is natural or dual and has a fixed complement
of dimension at most one. The preceding elementary-core result has Φ(R)=1,
so this displacement space is the actual group commutator [R,J].

The opposite SL₂ Levi shears generate the horizontal image of N, while the
previous identity [N,O₂(K)] = Z(O₂(K)) supplies its center. Hence [N,K]=N.
Comparing the order q³ with [R,J] gives [R,J]=[R,K]=N, including the degree-two
extension and both unitary orientations. All maps refer to the original
prepared overcomponent, and the Chapter12 companion applies the result there.

The second-parabolic construction and uniqueness contradiction, the remaining
maximality rows, exhaustive amalgam comparison and ambient recognition still
require proofs. Source: Aschbacher–Smith 5.2.8, printed pp.652–653, with
I.1.6(4), printed p.408 (`refs/quasithin.pdf`).
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySplit
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

private theorem model_H1 {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,F) V) (hF : 2 < Nat.card F)
    (hm : Nonempty (ρ.Equiv (naturalBinary F)) ∨ Nonempty (ρ.Equiv (dualBinary F))) :
    Subsingleton (H1 ρ) := by
  rcases hm with hn | hd
  · obtain ⟨e⟩ := hn
    let := SLHigherNatural.H1_subsingleton_sl3_large_field hF
    let : Subsingleton (H1 (naturalBinary F)) :=
      (H1RestrictEquiv (k := ZMod 2) (specialLinearNatural (k := F) 3)).injective.subsingleton
    exact (H1Congr ρ (naturalBinary F) (MulEquiv.refl _) e.toLinearEquiv
      (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v)).injective.subsingleton
  · obtain ⟨e⟩ := hd
    let e' := e.trans (dualBinaryEquiv F)
    let := SLHigherNatural.H1_subsingleton_sl3_dual_large_field hF
    let : Subsingleton (H1 (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3).dual)) :=
      (H1RestrictEquiv (k := ZMod 2) (specialLinearNatural (k := F) 3).dual).injective.subsingleton
    exact (H1Congr ρ (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3).dual) (MulEquiv.refl _) e'.toLinearEquiv
      (fun g v => LinearMap.congr_fun (e'.isIntertwining' g) v)).injective.subsingleton

private theorem simple_H1 {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,F) V) [ρ.IsIrreducible]
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m)
    (hn : ∃ g, ρ g ≠ 1) (hd : Module.finrank (ZMod 2) V ≤ 3*m+1) :
    Subsingleton (H1 ρ) := by
  let := ZMod.algebra F 2
  obtain ⟨hs,ha | ht | hg⟩ := AbsoluteExhaustion.absolute_model_trichotomy ρ hn m (by omega) hF
  · obtain ⟨hs,hdim,hmodel⟩ := ha
    apply model_H1 ρ
    · rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hm)
    · exact descend_absolute_natural ρ m hF hs hmodel
  · obtain ⟨hn,he,_⟩ := ht
    omega
  · omega

private theorem small_action_trivial {A V : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (hd : Module.finrank (ZMod 2) V ≤ 1) :
    ∀ g v, ρ g v = v := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hc : Nat.card V ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hd).trans_eq (by decide)
  intro g v
  by_cases hv : v = 0
  · simp [hv]
  have hn : ρ g v ≠ 0 := by
    intro he
    apply hv
    have hh := congrArg (fun w => ρ g⁻¹ w) he
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply,map_zero] using hh
  have ht : Nat.card V = 2 := by
    let : Nontrivial V := ⟨v,0,hv⟩
    apply le_antisymm hc
    let := Fintype.ofFinite V
    have hb : 1 < Nat.card V := by
      simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := V))
    omega
  obtain ⟨w,hw,huniq⟩ := (Nat.card_eq_two_iff' (0 : V)).mp ht
  exact (huniq _ hn).trans (huniq _ hv).symm


private def moved {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) : Subrepresentation ρ where
  toSubmodule := Coinvariants.ker ρ
  apply_mem_toSubmodule g v hv := by
    simpa only [sub_add_cancel] using
      (Coinvariants.ker ρ).add_mem (Coinvariants.sub_mem_ker g v) hv

private theorem simple_moved {A V : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) [ρ.IsIrreducible]
    (hn : ∃ g, ρ g ≠ 1) : Coinvariants.ker ρ = ⊤ := by
  rcases eq_bot_or_eq_top (moved ρ) with hz | ht
  · have hz' : Coinvariants.ker ρ = ⊥ := congrArg Subrepresentation.toSubmodule hz
    obtain ⟨g,hg⟩ := hn
    apply (hg ?_).elim
    ext v
    have hv := Coinvariants.sub_mem_ker (ρ := ρ) g v
    rw [hz',Submodule.mem_bot,sub_eq_zero] at hv
    exact hv
  · exact congrArg Subrepresentation.toSubmodule ht

private theorem simple_fixed {A V : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) [ρ.IsIrreducible]
    (hn : ∃ g, ρ g ≠ 1) : ρ.invariants = ⊥ := by
  let I : Subrepresentation ρ := {
    toSubmodule := ρ.invariants
    apply_mem_toSubmodule g v hv := by rw [hv g]; exact hv }
  rcases eq_bot_or_eq_top I with hz | ht
  · exact congrArg Subrepresentation.toSubmodule hz
  · have ht' : ρ.invariants = ⊤ := congrArg Subrepresentation.toSubmodule ht
    obtain ⟨g,hg⟩ := hn
    apply (hg ?_).elim
    ext v
    exact (show v ∈ ρ.invariants from ht' ▸ Submodule.mem_top) g

section Disjoint
variable {D U Q : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Q] [Module (ZMod 2) Q]
  {σ : Representation (ZMod 2) D U} {τ : Representation (ZMod 2) D Q}
private theorem range_H1 (i : σ.IntertwiningMap τ) (hi : Function.Injective i)
    [Subsingleton (H1 σ)] : Subsingleton (H1 i.range.toRepresentation) := by
  let l : U ≃ₗ[ZMod 2] i.range.toSubmodule := LinearEquiv.ofInjective i.toLinearMap hi
  have hl (g : D) (v : U) : l (σ g v) = i.range.toRepresentation g (l v) :=
    Subtype.ext (i.isIntertwining σ τ g v)
  exact (H1Congr σ i.range.toRepresentation (MulEquiv.refl D) l hl).symm.injective.subsingleton

private theorem range_fixed_supplement (i : σ.IntertwiningMap τ)
    (hi : Function.Injective i) (ht : HasTrivialQuotient i.range)
    [Subsingleton (H1 σ)] (v : Q) :
    ∃ u : U, ∃ z : Q, z ∈ τ.invariants ∧ i u + z = v := by
  let := range_H1 i hi
  have hv := (extensionClass_eq_zero_iff i.range ht v).mp (Subsingleton.elim _ _)
  obtain ⟨_, ⟨u,rfl⟩, z, hz, he⟩ := Submodule.mem_sup.mp hv
  exact ⟨u,z,hz,he⟩

private theorem central_kernel_disjoint
    (p : σ.IntertwiningMap τ) (hs : Function.Surjective p)
    (hc : p.toLinearMap.ker ≤ σ.invariants) [Subsingleton (H1 τ.dual)] :
    Disjoint (Coinvariants.ker σ) p.toLinearMap.ker := by
  let i : τ.dual.IntertwiningMap σ.dual := dualIntertwining p
  have ht : HasTrivialQuotient i.range := by
    intro g f
    change σ.dual g f - f ∈ p.toLinearMap.dualMap.range
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro w hw
    change f (σ g⁻¹ w) - f w = 0
    rw [(hc hw) g⁻¹, sub_self]
  rw [Submodule.disjoint_def]
  intro x hx hk
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) x).mp
  intro f
  obtain ⟨b,z,hz,rfl⟩ := range_fixed_supplement (σ := τ.dual) (τ := σ.dual) i
    (LinearMap.dualMap_injective_of_surjective (f := p.toLinearMap) hs) ht f
  have hz' : z ∈ (Coinvariants.ker σ).dualAnnihilator := by
    rw [← σ.invariants_dual_eq_commutator_annihilator]
    exact hz
  change b (p x) + z x = 0
  have hzx : z x = 0 := by
    rw [Submodule.mem_dualAnnihilator] at hz'
    exact hz' x hx
  rw [show p x = 0 from hk, map_zero, hzx, add_zero]

end Disjoint

private theorem central_split {A V W : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) A V} {τ : Representation (ZMod 2) A W}
    (p : ρ.IntertwiningMap τ) (hs : Function.Surjective p)
    (hc : p.toLinearMap.ker ≤ ρ.invariants)
    (hgen : Coinvariants.ker τ = ⊤) (hfix : τ.invariants = ⊥)
    [Subsingleton (H1 τ.dual)] :
    Nonempty ((moved ρ).toRepresentation.Equiv τ) ∧
      IsCompl (Coinvariants.ker ρ) ρ.invariants := by
  have hdis := central_kernel_disjoint p hs hc
  have hmap : (Coinvariants.ker ρ).map p.toLinearMap = ⊤ := by
    apply top_unique
    rw [←hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    obtain ⟨w,rfl⟩ := hs v
    exact ⟨ρ g w - w,Coinvariants.sub_mem_ker g w,by
      change p (ρ g w - w) = τ g (p w) - p w
      rw [map_sub,p.isIntertwining]⟩
  let q : (moved ρ).toRepresentation.IntertwiningMap τ :=
    .mk (p.toLinearMap.comp (Coinvariants.ker ρ).subtype) (by
      intro g; ext v; exact p.isIntertwining ρ τ g v)
  have hqi : Function.Injective q := by
    apply (injective_iff_map_eq_zero q).mpr
    intro v hv
    exact Subtype.ext (Submodule.disjoint_def.mp hdis v v.property hv)
  have hqs : Function.Surjective q := by
    intro w
    have hw : w ∈ (Coinvariants.ker ρ).map p.toLinearMap := hmap ▸ Submodule.mem_top
    obtain ⟨v,hv,he⟩ := hw
    exact ⟨⟨v,hv⟩,he⟩
  refine ⟨⟨q.ofBijective ⟨hqi,hqs⟩⟩,?_,?_⟩
  · apply Submodule.disjoint_def.mpr
    intro v hv hf
    apply Submodule.disjoint_def.mp hdis v hv
    have hpfix : p v ∈ τ.invariants := by intro g; rw [←p.isIntertwining,hf g]
    change p v = 0
    simpa only [hfix,Submodule.mem_bot] using hpfix
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    obtain ⟨w,hw⟩ := hqs (p v)
    have hker : v - w.val ∈ p.toLinearMap.ker := by
      change p (v-w.val) = 0
      rw [map_sub,show p w.val = p v from hw,sub_self]
    exact Submodule.mem_sup.mpr ⟨w,w.property,v-w.val,hc hker,by abel⟩


private theorem simple_nontrivial {A V : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) [ρ.IsIrreducible]
    (hd : 2 ≤ Module.finrank (ZMod 2) V) : ∃ g, ρ g ≠ 1 := by
  by_contra! hh
  have hf := fixed_eq_bot_of_irreducible_finrank ρ hd
  have he : (⊤ : Submodule (ZMod 2) V) ≤ fixed ρ := by
    intro v _ g
    rw [hh g]
    rfl
  rw [hf] at he
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  exact top_ne_bot (le_antisymm he bot_le)

private theorem moved_eq_of_split {A V : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (U : Subrepresentation ρ)
    (hg : Coinvariants.ker U.toRepresentation = ⊤)
    (ht : HasTrivialQuotient U) : U.toSubmodule = Coinvariants.ker ρ := by
  apply le_antisymm
  · have hle : Coinvariants.ker U.toRepresentation ≤
        (Coinvariants.ker ρ).comap U.toSubmodule.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := ρ) g v
    rw [hg] at hle
    intro v hv
    exact hle (show (⟨v,hv⟩ : U.toSubmodule) ∈ ⊤ from Submodule.mem_top)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    exact ht g v

private theorem section_split {A V : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (U : Subrepresentation ρ)
    (N : Subrepresentation U.toRepresentation)
    [N.quotientRepresentation.IsIrreducible]
    (hn : ∃ g, N.quotientRepresentation g ≠ 1)
    (hd : Module.finrank (ZMod 2) V ≤
      Module.finrank (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule) + 1)
    [Subsingleton (H1 N.quotientRepresentation)]
    [Subsingleton (H1 N.quotientRepresentation.dual)] :
    ∃ C : Subrepresentation ρ, C.toSubmodule = Coinvariants.ker ρ ∧
      Nonempty (C.toRepresentation.Equiv N.quotientRepresentation) ∧
      IsCompl C.toSubmodule ρ.invariants := by
  let q : U.toRepresentation.IntertwiningMap N.quotientRepresentation :=
    .mk N.toSubmodule.mkQ (by intro g; rfl)
  have hdim := N.toSubmodule.finrank_quotient_add_finrank
  have hU := Submodule.finrank_le U.toSubmodule
  have hUdim := U.toSubmodule.finrank_quotient_add_finrank
  have hNdim : Module.finrank (ZMod 2) N.toSubmodule ≤ 1 := by omega
  by_cases hNz : N.toSubmodule = ⊥
  · have hqi : Function.Injective q := by
      apply (injective_iff_map_eq_zero q).mpr
      intro v hv
      have hh := (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp hv
      simpa only [hNz,Submodule.mem_bot] using hh
    let e := q.ofBijective ⟨hqi,N.toSubmodule.mkQ_surjective⟩
    let : U.toRepresentation.IsIrreducible :=
      (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv inferInstance
    have hnU : ∃ g, U.toRepresentation g ≠ 1 := by
      obtain ⟨g,hg⟩ := hn
      refine ⟨g,fun he => hg ?_⟩
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := e.toLinearEquiv.surjective v
      change N.quotientRepresentation g (e w) = e w
      have hh := LinearMap.congr_fun (e.isIntertwining' g) w
      change e (U.toRepresentation g w) = N.quotientRepresentation g (e w) at hh
      rw [he] at hh
      exact hh.symm
    let : Subsingleton (H1 U.toRepresentation) :=
      (H1Congr U.toRepresentation N.quotientRepresentation (MulEquiv.refl A) e.toLinearEquiv
        (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v)).injective.subsingleton
    have htdim : Module.finrank (ZMod 2) (V ⧸ U.toSubmodule) ≤ 1 := by
      have hedim := e.toLinearEquiv.finrank_eq
      omega
    have ht : HasTrivialQuotient U := by
      intro g v
      apply (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp
      change U.toSubmodule.mkQ (ρ g v-v) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (small_action_trivial U.quotientRepresentation htdim g
        (U.toSubmodule.mkQ v))
    refine ⟨U,moved_eq_of_split ρ U (simple_moved _ hnU) ht,⟨e⟩,?_,?_⟩
    · apply Submodule.disjoint_def.mpr
      intro v hv hf
      have hh : (⟨v,hv⟩ : U.toSubmodule) ∈ U.toRepresentation.invariants :=
        fun g => Subtype.ext (hf g)
      rw [simple_fixed _ hnU,Submodule.mem_bot] at hh
      exact congrArg Subtype.val hh
    · apply codisjoint_iff.mpr
      apply top_unique
      intro v _
      exact (extensionClass_eq_zero_iff U ht v).mp (Subsingleton.elim _ _)
  · have hNd : 0 < Module.finrank (ZMod 2) N.toSubmodule :=
      Nat.pos_of_ne_zero (mt Submodule.finrank_eq_zero.mp hNz)
    have hUt : U.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    let i : U.toRepresentation.IntertwiningMap ρ :=
      .mk U.toSubmodule.subtype (by intro g; rfl)
    let e := i.ofBijective ⟨Subtype.val_injective,by
      intro v; exact ⟨⟨v,hUt ▸ Submodule.mem_top⟩,rfl⟩⟩
    let p := q.comp e.symm.toIntertwiningMap
    have hp : Function.Surjective p := N.toSubmodule.mkQ_surjective.comp e.symm.toLinearEquiv.surjective
    have hc : p.toLinearMap.ker ≤ ρ.invariants := by
      intro v hv g
      have hnmem : e.symm v ∈ N := (Submodule.Quotient.mk_eq_zero _).mp hv
      have he := small_action_trivial N.toRepresentation hNdim g
        (⟨e.symm v,hnmem⟩ : N.toSubmodule)
      have he' : U.toRepresentation g (e.symm v) = e.symm v := congrArg Subtype.val he
      have hh := LinearMap.congr_fun (e.isIntertwining' g) (e.symm v)
      change e (U.toRepresentation g (e.symm v)) = ρ g (e (e.symm v)) at hh
      rw [he',e.apply_symm_apply] at hh
      exact hh.symm
    obtain ⟨he,hcompl⟩ := central_split p hp hc (simple_moved _ hn) (simple_fixed _ hn)
    exact ⟨moved ρ,rfl,he,hcompl⟩


/-- The natural or dual moved part of the literal core action, with its
fixed complement and the actual quotient identification retained. -/
@[expose] def SplitCoreAction {G : Type*} [Group G] [Finite G] (h : HasCharacteristicTwo G) (m : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    Nat.card F = 2^m ∧ ∃ e : (G ⧸ pCore 2 G) ≃* SL(3,F),
    ∃ C : Subrepresentation (UnitaryCover.frattiniAction h),
      C.toSubmodule = Coinvariants.ker (UnitaryCover.frattiniAction h) ∧
      IsCompl C.toSubmodule (UnitaryCover.frattiniAction h).invariants ∧
      Module.finrank (ZMod 2) C.toSubmodule = 3*m ∧
      Module.finrank (ZMod 2) (UnitaryCover.frattiniAction h).invariants ≤ 1 ∧
      (let := ZMod.algebra F 2
       Nonempty (Representation.Equiv (C.toRepresentation.comp e.symm.toMonoidHom) (naturalBinary F)) ∨
       Nonempty (Representation.Equiv (C.toRepresentation.comp e.symm.toMonoidHom) (dualBinary F)))

private theorem H1_of_comp {A B V : Type*} [Group A] [Group B]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (e : A ≃* B)
    [Subsingleton (H1 (ρ.comp e.symm.toMonoidHom))] : Subsingleton (H1 ρ) := by
  have he (g : A) (v : V) : (LinearEquiv.refl (ZMod 2) V) (ρ g v) =
      (ρ.comp e.symm.toMonoidHom) (e g) ((LinearEquiv.refl (ZMod 2) V) v) := by
    change ρ g v = ρ (e.symm (e g)) v
    rw [e.symm_apply_apply]
  exact (H1Congr ρ (ρ.comp e.symm.toMonoidHom) e (LinearEquiv.refl (ZMod 2) V) he).injective.subsingleton

/-- The original bounded core action splits into its entire natural or dual
commutator module and at most one fixed binary dimension. This includes the
extra dimension allowed by the degree-two unitary extension. -/
theorem split_core {G : Type*} [Group G] [Finite G]
    {h : HasCharacteristicTwo G} {m : ℕ} (hm : 1 < m)
    (d : UnitaryCover.NaturalCoreSection h m)
    (hc : Nat.card (pCore 2 G) ≤ 2*(2^m)^3) : SplitCoreAction h m := by
  have hdV : Module.finrank (ZMod 2) (UnitaryCover.CoreSpace G) ≤ 3*m+1 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := UnitaryCover.CoreSpace G)
    rw [Nat.card_zmod] at hcard
    rw [←hcard]
    have hb := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini (pCore 2 G)))
      (QuotientGroup.mk'_surjective _)
    change Nat.card ((pCore 2 G) ⧸ frattini (pCore 2 G)) ≤ _
    calc
      _ ≤ Nat.card (pCore 2 G) := hb
      _ ≤ 2*(2^m)^3 := hc
      _ = 2^(3*m+1) := by rw [←pow_mul,Nat.mul_comm m 3,pow_succ]; omega
  obtain ⟨F,_,_,_,hF,e,U,N,hi,hfaith,hdegree,hmodel⟩ := d.exists_section
  let := hi
  let τ : Representation (ZMod 2) SL(3,F) (U.toSubmodule ⧸ N.toSubmodule) :=
    N.quotientRepresentation.comp e.symm.toMonoidHom
  let : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr hi
  let : τ.dual.IsIrreducible := isIrreducible_dual
  have hd : Module.finrank (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule) ≤ 3*m+1 := by omega
  let : Subsingleton (H1 τ) := simple_H1 τ hm hF (simple_nontrivial τ (by omega)) hd
  let : Subsingleton (H1 τ.dual) := simple_H1 τ.dual hm hF
    (simple_nontrivial τ.dual (by rw [Subspace.dual_finrank_eq]; omega))
    (by rw [Subspace.dual_finrank_eq]; exact hd)
  let : Subsingleton (H1 N.quotientRepresentation) := H1_of_comp _ e
  have hdual : τ.dual = N.quotientRepresentation.dual.comp e.symm.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (N.quotientRepresentation (e.symm g⁻¹) v) =
      f (N.quotientRepresentation (e.symm g)⁻¹ v)
    rw [map_inv]
  let : Subsingleton (H1 (N.quotientRepresentation.dual.comp e.symm.toMonoidHom)) :=
    hdual ▸ (inferInstance : Subsingleton (H1 τ.dual))
  let : Subsingleton (H1 N.quotientRepresentation.dual) := H1_of_comp _ e
  obtain ⟨C,hC,⟨a⟩,hcompl⟩ := section_split (UnitaryCover.frattiniAction h) U N
    (simple_nontrivial _ (by omega)) (by omega)
  have hCd : Module.finrank (ZMod 2) C.toSubmodule = 3*m :=
    a.toLinearEquiv.finrank_eq.trans hdegree
  have hId : Module.finrank (ZMod 2) (UnitaryCover.frattiniAction h).invariants ≤ 1 := by
    have he := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  refine ⟨F,inferInstance,inferInstance,inferInstance,hF,e,C,hC,hcompl,hCd,hId,?_⟩
  let := ZMod.algebra F 2
  let b : Representation.Equiv (C.toRepresentation.comp e.symm.toMonoidHom)
      (N.quotientRepresentation.comp e.symm.toMonoidHom) :=
    .mk a.toLinearEquiv (fun g => a.isIntertwining' (e.symm g))
  rcases hmodel with hn | hd
  · obtain ⟨c⟩ := hn
    exact .inl ⟨b.trans c⟩
  · obtain ⟨c⟩ := hd
    exact .inr ⟨b.trans c⟩


/-- With trivial Frattini subgroup, the moved part is the literal group
commutator [O₂(G),G], of order q³. -/
theorem SplitCoreAction.moved_card {G : Type*} [Group G] [Finite G]
    {h : HasCharacteristicTwo G} {m : ℕ} (d : SplitCoreAction h m)
    (hphi : frattini (pCore 2 G) = ⊥) :
    Nat.card (⁅pCore 2 G,(⊤ : Subgroup G)⁆ : Subgroup G) = (2^m)^3 := by
  let R := pCore 2 G
  let E := R ⧸ frattini R
  let q := QuotientGroup.mk' (frattini R)
  let a := QuotientGroup.mk' R
  let β := (quotientAut (frattini R)).comp (MulAut.conjNormal : G →* MulAut R)
  let α := QuotientGroup.lift R β (pCore_frattini_action_kernel 2 h).ge
  have hα (g : G) (r : R) : α (a g) (q r) = q (MulAut.conjNormal g r) :=
    quotientAut_apply_mk (frattini R) (MulAut.conjNormal g) r
  have hρ : ProjectiveRadicalSplitting.linearAction α = UnitaryCover.frattiniAction h := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective R g
    rw [ProjectiveRadicalSplitting.linearAction_apply]
    exact (UnitaryCover.frattiniAction_apply h g v.toMul).symm
  have he := ProjectiveRadicalSplitting.commutatorImage_eq_coinvariants R a
    (QuotientGroup.mk'_surjective R) q (QuotientGroup.mk'_surjective _) α hα
  rw [hρ] at he
  have hqi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk',hphi]
  obtain ⟨F,_,_,_,hF,e,C,hC,hcompl,hdegree,hfixed,hmodel⟩ := d
  have hcc : Nat.card (Coinvariants.ker (UnitaryCover.frattiniAction h)) = (2^m)^3 := by
    rw [←hC,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdegree]
    rw [←pow_mul,Nat.mul_comm m 3]
  calc
    Nat.card (⁅R,(⊤ : Subgroup G)⁆ : Subgroup G) = Nat.card (⁅R,(⊤ : Subgroup G)⁆.subgroupOf R) :=
      (Nat.card_congr (subgroupOfEquivOfLe (commutator_le_left R ⊤)).toEquiv).symm
    _ = Nat.card ((⁅R,(⊤ : Subgroup G)⁆.subgroupOf R).map q) :=
      Nat.card_congr ((⁅R,(⊤ : Subgroup G)⁆.subgroupOf R).equivMapOfInjective q hqi).toEquiv
    _ = Nat.card (Coinvariants.ker (UnitaryCover.frattiniAction h)) := by rw [←he]; rfl
    _ = (2^m)^3 := hcc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitarySplit

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- In the original proper unitary branch, including the degree-two extension,
the entire moved core is a natural or dual module of order q³. The only
remaining part of the elementary full core is fixed and has rank at most one. -/
theorem Preparation.unitary_overcomponent_split_core
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    IsElementaryAbelian 2 (J.pCoreIn 2) ∧ frattini (pCore 2 J) = ⊥ ∧
      Nat.card (⁅J.pCoreIn 2,J⁆ : Subgroup G) = (2^m)^3 ∧
      ∃ hc : HasCharacteristicTwo J, UnitarySplit.SplitCoreAction hc m := by
  obtain ⟨helem,hphi⟩ := d.unitary_overcomponent_elementary_core h hH hp m hm he hJ hKJ hQR
  obtain ⟨_,_,hc,hsection⟩ := d.unitary_overcomponent_full_linear_action h hH hp m hm he hJ hKJ hQR
  have hb := (d.unitary_overcomponent_proper_image_block h hH hp m hm he hJ hKJ.le hQR).1
  have hR := (d.unitary_overcomponent_proper_quotient_core h hH hp m hm he hJ hKJ.le hQR).2
  have hR' : Nat.card (pCore 2 J) ≤ 2*(2^m)^3 := by
    rw [Nat.card_congr ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv]
    exact hR
  have hsplit := UnitarySplit.split_core hb.1 hsection hR'
  refine ⟨helem,hphi,?_,hc,hsplit⟩
  have hcard := hsplit.moved_card hphi
  have hmap : (⁅pCore 2 J,(⊤ : Subgroup J)⁆).map J.subtype = ⁅J.pCoreIn 2,J⁆ := by
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rfl
  rw [←hmap,card_map_of_injective J.subtype_injective]
  exact hcard

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global


namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryIntersectionGeneration
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
open scoped commutatorElement
variable (F : Type*) [Field F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "k" => FixedBy.subfield F σ
local notation "κ" => coordinatesOfRadical F σ hσ

private def horizontal : R →* Multiplicative (F × F) where
  toFun a := Multiplicative.ofAdd ((κ a).x,(κ a).y)
  map_one' := rfl
  map_mul' a b := by
    obtain ⟨c,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
    obtain ⟨d,rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective b
    have he := radical_mul_coordinates F σ hσ c d
    exact congrArg Multiplicative.ofAdd (Prod.ext he.1 he.2.1)

private theorem normal_core_moved (hnt : ∃ u, σ u ≠ u)
    (N : Subgroup L) (hn : N.Normal) (hN : N ≤ R)
    (hz : (center R).map (radical F σ hσ).subtype ≤ ⁅N,(⊤ : Subgroup L)⁆) :
    ⁅N,(⊤ : Subgroup L)⁆ = N := by
  let := hn
  let C := ⁅N,(⊤ : Subgroup L)⁆
  have hCN : C ≤ N := commutator_le_left _ _
  have hCR : C ≤ R := hCN.trans hN
  let f := horizontal F σ hσ
  let W := ((C.subgroupOf R).map f).toAddSubgroup'
  have hW (x y : F) : (x,y) ∈ W ↔
      ∃ r : R, r.val ∈ C ∧ (κ r).x = x ∧ (κ r).y = y := by
    constructor
    · rintro ⟨r,hr,he⟩
      exact ⟨r,hr,congrArg (fun z => z.toAdd.1) he,congrArg (fun z => z.toAdd.2) he⟩
    · rintro ⟨r,hr,hx,hy⟩
      exact ⟨r,hr,congrArg Multiplicative.ofAdd (Prod.ext hx hy)⟩
  have hs (r : R) (hr : r.val ∈ N) (upper : Bool) :
      (if upper then ((κ r).y,0) else (0,(κ r).x)) ∈ W := by
    let M : SpecialLinearGroup (Fin 2) k :=
      ⟨if upper then !![1,1;0,1] else !![1,0;1,1],by
        cases upper <;> simp [Matrix.det_fin_two]⟩
    let l := leviSL F σ hσ M
    let b := leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm M) (κ r)
    have hb : b.val = l * r.val * l⁻¹ := by
      change _ * (radicalOfCoordinates F σ hσ (κ r)).val * _ = _
      rw [show radicalOfCoordinates F σ hσ (κ r) = r from
        (radicalCoordinatesEquiv F σ hσ).apply_symm_apply r]
      rfl
    have hc : (b*r⁻¹ : R).val ∈ C := by
      change b.val * r.val⁻¹ ∈ C
      rw [hb]
      change ⁅l,r.val⁆ ∈ ⁅N,(⊤ : Subgroup L)⁆
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_top l) hr
    have hw : (f (b*r⁻¹)).toAdd ∈ W := ⟨b*r⁻¹,hc,rfl⟩
    rw [map_mul,map_inv] at hw
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg] at hw
    have he := leviSL_conjugation_coordinates F σ hσ M (κ r)
    change ((κ b).x - (κ r).x,(κ b).y - (κ r).y) ∈ W at hw
    change (κ b).x = _ ∧ (κ b).y = _ ∧ _ at he
    rw [he.1,he.2.1] at hw
    cases upper <;> simpa [M] using hw
  apply le_antisymm hCN
  intro a ha
  let r : R := ⟨a,hN ha⟩
  have hfirst := hs r ha true
  have hsecond := hs r ha false
  simp only [Bool.false_eq_true,if_false,if_true] at hfirst hsecond
  obtain ⟨b,hb,hbx,hby⟩ := (hW _ _).mp hsecond
  obtain ⟨c,hc,hcx,hcy⟩ := (hW _ _).mp hfirst
  have hx := hs b (hCN hb) true
  have hy := hs c (hCN hc) false
  simp only [Bool.false_eq_true,if_false,if_true,hby,hcx] at hx hy
  have hxy : ((κ r).x,(κ r).y) ∈ W := by simpa using W.add_mem hx hy
  obtain ⟨s,hsC,hsx,hsy⟩ := (hW _ _).mp hxy
  have heq : f r = f s := congrArg Multiplicative.ofAdd (Prod.ext hsx.symm hsy.symm)
  have hzker : r*s⁻¹ ∈ f.ker := by
    change f (r*s⁻¹)=1
    rw [map_mul,map_inv,heq,mul_inv_cancel]
  have hcenter : r*s⁻¹ ∈ center R := by
    apply (mem_center_radical_iff F σ hσ hnt _).mpr
    exact Prod.ext_iff.mp hzker
  have hm := C.mul_mem (hz (mem_map_of_mem (radical F σ hσ).subtype hcenter)) hsC
  change (r.val*s.val⁻¹)*s.val ∈ C at hm
  simpa only [inv_mul_cancel_right] using hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryIntersectionGeneration


namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryIntersectionGeneration
private theorem point_core_moved
    {X : Type*} [Group X] [Finite X] (m : ℕ) (hm : 1 ≤ m)
    (e : X ≃* ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.ProjectiveLocal m hm)
    (N : Subgroup X) [N.Normal] (hN : N ≤ pCore 2 X)
    (hz : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ ⁅N,(⊤ : Subgroup X)⁆) :
    ⁅N,(⊤ : Subgroup X)⁆ = N := by
  let F := ChapterF.GreenBook.LieModels.UnitaryFour.MatrixField m
  let σ := ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj m
  let hσ := ChapterF.GreenBook.LieModels.UnitaryFour.fieldConj_involutive m hm
  let P := pCore 2 X
  let R : Subgroup (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.MatrixLocal m hm) :=
    ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.Radical m hm
  let a := e.trans (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.localEquiv m hm).symm
  have hPR : P.map a.toMonoidHom = R := (pCore_map_iso 2 a).trans
    (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.radical_eq_twoCore m hm).symm
  have hnorm : (N.map a.toMonoidHom).Normal := Normal.map inferInstance a.toMonoidHom a.surjective
  have hatop : (⊤ : Subgroup X).map a.toMonoidHom = ⊤ := by
    rw [←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr a.surjective
  have hNR : N.map a.toMonoidHom ≤ R := (map_mono hN).trans_eq hPR
  have hzR : (center R).map R.subtype ≤ ⁅N.map a.toMonoidHom,⊤⁆ := by
    rw [←hPR,←map_embeddedCenter P a.toMonoidHom a.injective]
    have hh := map_mono (f := a.toMonoidHom) hz
    rw [map_commutator,hatop] at hh
    exact hh
  have he := normal_core_moved F σ hσ
    (ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal.fieldConj_nontrivial m hm)
    (N.map a.toMonoidHom) hnorm hNR hzR
  apply (Subgroup.map_injective (f := a.toMonoidHom) a.injective)
  rw [map_commutator,hatop]
  exact he
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryIntersectionGeneration

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he


/-- The original intersection is generated by its commutators with K.
The Levi shears generate its horizontal image, and [N,Q] supplies Z(Q). -/
theorem Preparation.unitary_overcomponent_intersection_generated
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H ≤ J) :
    ⁅residual H ⊓ J.pCoreIn 2,residual H⁆ = residual H ⊓ J.pCoreIn 2 := by
  let K := residual H
  let P := pCore 2 K
  let Q := K.pCoreIn 2
  let R := J.pCoreIn 2
  let N := R.subgroupOf K
  obtain ⟨_,hNQ,_,hNZ,_,_⟩ :=
    d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ
  have hNP : N ≤ P := fun x hx => (mem_map_iff_mem K.subtype_injective).mp
    (hNQ ⟨x.property,hx⟩)
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hKJ.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))
  have hmap : (⁅N,(⊤ : Subgroup K)⁆).map K.subtype = ⁅K ⊓ R,K⁆ := by
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype,subgroupOf_map_subtype,inf_comm R K]
  have hZ : ((center P).map P.subtype).map K.subtype = (center Q).map Q.subtype :=
    map_embeddedCenter P K.subtype K.subtype_injective
  have hz : (center P).map P.subtype ≤ ⁅N,(⊤ : Subgroup K)⁆ := by
    intro x hx
    have hxZ := mem_map_of_mem K.subtype hx
    rw [hZ,←hNZ] at hxZ
    have hxC := (commutator_mono le_rfl (pCoreIn_le 2 K)) hxZ
    rw [←hmap] at hxC
    exact (mem_map_iff_mem K.subtype_injective).mp hxC
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  obtain ⟨e⟩ := hf.2.2.2.1
  have hn := UnitaryIntersectionGeneration.point_core_moved m hm e N hNP hz
  rw [←hmap,hn]
  exact (subgroupOf_map_subtype R K).trans (inf_comm R K)

/-- Both original commutators equal the same intersection of order q³,
including the degree-two unitary extension. -/
theorem Preparation.unitary_overcomponent_moved_eq_intersection
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    ⁅J.pCoreIn 2,J⁆ = residual H ⊓ J.pCoreIn 2 ∧
      ⁅J.pCoreIn 2,residual H⁆ = residual H ⊓ J.pCoreIn 2 := by
  have hgen := d.unitary_overcomponent_intersection_generated h hH hp m hm he hJ hKJ.le
  have hNc := (d.unitary_overcomponent_proper_intersection h hH hp m hm he hJ hKJ.le hQR).2
  have hMc := (d.unitary_overcomponent_split_core h hH hp m hm he hJ hKJ hQR).2.2.1
  have hNM : residual H ⊓ J.pCoreIn 2 ≤ ⁅J.pCoreIn 2,J⁆ := by
    rw [←hgen]
    exact commutator_mono inf_le_right hKJ.le
  have heq : residual H ⊓ J.pCoreIn 2 = ⁅J.pCoreIn 2,J⁆ :=
    eq_of_le_of_card_ge hNM (by rw [hMc,hNc])
  refine ⟨heq.symm,le_antisymm ?_ ?_⟩
  · exact (commutator_mono le_rfl hKJ.le).trans_eq heq.symm
  · rw [←hgen]
    exact commutator_mono inf_le_right le_rfl

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
