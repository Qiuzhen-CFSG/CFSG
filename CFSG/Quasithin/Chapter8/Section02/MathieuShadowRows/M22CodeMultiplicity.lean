module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePairAction
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeCommutant
public import Theory.Representation.ScalarMultiplicity.Kernel
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.SL2.BinaryDihedral

/-!
# The M22 quintet multiplicity action

The two-copy M22 quintet section carries a commuting scalar multiplicity
operator on a binary plane. Its faithful quotient is forced by the selected
odd prime-power dihedral source to be PSL₂(2), retaining the literal section,
quotient maps, kernels and original conjugator used by later tensor arguments.
Source: Aschbacher--Smith 8.2.8(5), pp.718--719, refs/quasithin.pdf.
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction Normalizer.SmallOvergroups
public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]

@[expose] def M22CodePairMultiplicityAction (R I V U : Subgroup G) (i : I)
    (fq : R →* MathieuCode.M22Quintet.Q) : Prop :=
  let W := MathieuCode.M22Quintet.K
  let B := V ⊓ I.pCoreIn 2
  let Y := R ⊔ I
  ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
    ∃ hYU : Y ≤ normalizer (U : Set G),
      ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
        ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
          ∃ eB : (B ⧸ U.subgroupOf B) ≃* W,
            ∃ r : R →* alternatingGroup (Fin 5),
              ∃ eP : W × W ≃* (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
                ∃ μ : Representation (ZMod 2) (I ⧸ pCore 2 I) (Fin 2 → ZMod 2),
                let q := QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl)
                  (show B ≤ I.pCoreIn 2 from inf_le_right)
                let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
                Function.Surjective r ∧ r.ker = pCore 2 R ∧
                (∀ x, (r x).val = MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient.q (fq x)) ∧
                Function.Injective μ.asGroupHom ∧
                (∀ x y, eP (x,y) = q (eB.symm x) * f (inclusion le_sup_right i⁻¹) (q (eB.symm y))) ∧
                (∀ (x : R) u v, f (inclusion le_sup_left x) (eP (u,v)) =
                  eP ((MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x)
                      (Additive.ofMul u)).toMul,
                    (MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x)
                      (Additive.ofMul v)).toMul)) ∧
                ∀ (a : I) (c : Fin 2 → ZMod 2) (v : Additive W),
                  f (inclusion le_sup_right a) (eP ((c 0 • v).toMul,(c 1 • v).toMul)) =
                    eP ((μ (QuotientGroup.mk' (pCore 2 I) a) c 0 • v).toMul,
                      (μ (QuotientGroup.mk' (pCore 2 I) a) c 1 • v).toMul)

omit [Finite G] in
theorem m22_code_pair_multiplicity_action (R I V U : Subgroup G) (i : I) {fq : R →* MathieuCode.M22Quintet.Q}
    (hp : M22CodePairProductAction R I V U) (hn : M22CodePairAction R I V U i fq)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2) : M22CodePairMultiplicityAction R I V U i fq := by
  obtain ⟨hYP,hYU,hUP,hBU,eB,rA,eP,hrsur,hrker,hrval,heP,hR⟩ := hn
  let := hUP
  let := hBU
  obtain ⟨_,_,_,hEl,hcard,hker,hcore,hRker,hIker,_⟩ := hp
  let := hEl
  let W := MathieuCode.M22Quintet.K
  let X := Fin 2 → (Additive MathieuCode.M22Quintet.K)
  let P := I.pCoreIn 2
  let Y := R ⊔ I
  let f := sectionAction Y P U hYP hYU
  let e : Multiplicative X ≃* (P ⧸ U.subgroupOf P) :=
    (LinearEquiv.finTwoArrow (ZMod 2) (Additive MathieuCode.M22Quintet.K)).toAddEquiv.toMultiplicative.trans
      ((MulEquiv.prodMultiplicative _ _).trans
        ((MulEquiv.toMultiplicative_toAdditive.prodCongr MulEquiv.toMultiplicative_toAdditive).trans eP))
  let a : I →* MulAut (Multiplicative X) :=
    (MulAut.congr e.symm).toMonoidHom.comp (f.comp (inclusion le_sup_right))
  let ρ : Representation (ZMod 2) I X := {
    toFun g := (AddMonoidHom.toMultiplicative.symm (a g).toMonoidHom).toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro x; change (a 1 (Multiplicative.ofAdd x)).toAdd = x; rw [map_one]; rfl
    map_mul' g h := by apply LinearMap.ext; intro x; change (a (g*h) (Multiplicative.ofAdd x)).toAdd = (a g (a h (Multiplicative.ofAdd x))).toAdd; rw [map_mul]; rfl }
  have hρ (g : I) (x : X) :
      e (Multiplicative.ofAdd (ρ g x)) = f (inclusion le_sup_right g) (e (Multiplicative.ofAdd x)) := by
    change e (e.symm _) = _
    exact e.apply_symm_apply _
  let σ := MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction
  have hc (g : I) (d : alternatingGroup (Fin 5)) (x : X) :
      ρ g (fun j => σ d (x j)) = fun j => σ d (ρ g x j) := by
    obtain ⟨r,hdr⟩ := hrsur d
    have hdiag (x : X) :
        e (Multiplicative.ofAdd (fun j => σ d (x j))) =
          f (inclusion le_sup_left r) (e (Multiplicative.ofAdd x)) := by
      change eP ((σ d (x 0)).toMul,(σ d (x 1)).toMul) =
        f (inclusion le_sup_left r) (eP ((x 0).toMul,(x 1).toMul))
      rw [hR,hdr]
      rfl
    have hfc : Commute (f (inclusion le_sup_left r)) (f (inclusion le_sup_right g)) := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      apply MonoidHom.mem_ker.mp
      rw [hker]
      have hm : (⁅(r : G),(g : G)⁆ : G) ∈ Y.pCoreIn 2 := by
        rw [hcore]
        exact mem_sup_right (hcomm (commutator_mem_commutator r.property g.property))
      obtain ⟨t,ht,he⟩ := hm
      have he' : t = ⁅inclusion (show R ≤ Y from le_sup_left) r,
          inclusion (show I ≤ Y from le_sup_right) g⁆ := Subtype.ext he
      exact he' ▸ ht
    apply Multiplicative.ofAdd.injective
    apply e.injective
    rw [hρ,hdiag,hdiag,hρ]
    exact congrArg (fun z : MulAut (P ⧸ U.subgroupOf P) => z (e (Multiplicative.ofAdd x))) hfc.eq.symm
  let : Nontrivial (Additive MathieuCode.M22Quintet.K) :=
    Module.nontrivial_of_finrank_pos (by rw [Sporadic.Mathieu.M22ChapterH.Quintet.kernel_finrank]; decide)
  obtain ⟨μ,hμ,hμker⟩ := ScalarMultiplicity.exists_multiplicity_kernel σ
    MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction_commuting_scalar ρ hc
  have hk : μ.asGroupHom.ker = pCore 2 I := by
    rw [hμker]
    ext g
    rw [←hIker]
    change ρ.asGroupHom g = 1 ↔ f (inclusion le_sup_right g) = 1
    constructor
    · intro hg
      apply MulEquiv.ext
      intro y
      obtain ⟨x,rfl⟩ := e.surjective y
      have hh := hρ g x.toAdd
      have hρg : ρ g = 1 := congrArg Units.val hg
      rw [hρg] at hh
      exact hh.symm
    · intro hg
      apply Units.ext
      apply LinearMap.ext
      intro x
      change ρ g x = x
      apply Multiplicative.ofAdd.injective
      apply e.injective
      rw [hρ,hg]
      rfl
  let μq := QuotientGroup.lift (pCore 2 I) μ.asGroupHom hk.ge
  have hi : Function.Injective μq := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_lift,hk]
    exact QuotientGroup.map_mk'_self _
  let ν : Representation (ZMod 2) (I ⧸ pCore 2 I) (Fin 2 → ZMod 2) :=
    (Units.coeHom (Module.End (ZMod 2) (Fin 2 → ZMod 2))).comp μq
  have hν (g : I) (c : Fin 2 → ZMod 2) (v : Additive MathieuCode.M22Quintet.K) :
      f (inclusion le_sup_right g) (eP ((c 0 • v).toMul, (c 1 • v).toMul)) =
        eP ((ν (QuotientGroup.mk' (pCore 2 I) g) c 0 • v).toMul,
          (ν (QuotientGroup.mk' (pCore 2 I) g) c 1 • v).toMul) := by
    have hh := hρ g (fun j => c j • v)
    rw [hμ] at hh
    exact hh.symm
  refine ⟨hYP,hYU,hUP,hBU,eB,rA,eP,ν,hrsur,hrker,hrval,?_,heP,hR,hν⟩
  intro x y hxy
  apply hi
  apply Units.ext
  have hh := congrArg (fun z : (Module.End (ZMod 2) (Fin 2 → ZMod 2))ˣ => z.val) hxy
  exact hh


/-- A faithful action on the binary multiplicity plane forces the original
odd prime-power dihedral quotient to be L2(2). -/
theorem selected_m22_code_multiplicity_cubic
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    {fq : R →* MathieuCode.M22Quintet.Q}
    (hp : M22CodePairProductAction R I V U) (hn : M22CodePairAction R I V U i fq)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2) :
    M22CodePairMultiplicityAction R I V U i fq ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) := by
  have hm := m22_code_pair_multiplicity_action R I V U i hp hn hcomm
  refine ⟨hm,?_⟩
  obtain ⟨_,_,_,_,_,_,_,μ,_,_,_,hμ,_⟩ := hm
  rcases s.models with ⟨hk,_⟩ | ⟨m,hm,hk,_⟩ | ⟨_,p,a,hp,ho,ha,⟨d⟩⟩
  · omega
  · omega
  · let f : DihedralGroup (p^a) →* GL (Fin 2) (ZMod 2) :=
      Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
        (μ.asGroupHom.comp d.symm.toMonoidHom)
    have hf : Function.Injective f :=
      Matrix.GeneralLinearGroup.toLin.symm.injective.comp (hμ.comp d.symm.injective)
    let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have hd := card_dvd_of_injective f hf
    rw [DihedralGroup.nat_card,Matrix.card_GL_field] at hd
    norm_num [Fin.prod_univ_two] at hd
    have hpow : p^a ∣ 3 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hd
    have hn : 1 < p^a := Nat.one_lt_pow ha.ne' hp.one_lt
    have he : p^a = 3 := ((Nat.dvd_prime Nat.prime_three).mp hpow).resolve_left (by omega)
    have he' : Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 3) :=
      he ▸ (show Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup (p^a)) from ⟨d⟩)
    obtain ⟨d'⟩ := he'
    exact ⟨d'.trans Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two⟩

end
end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
