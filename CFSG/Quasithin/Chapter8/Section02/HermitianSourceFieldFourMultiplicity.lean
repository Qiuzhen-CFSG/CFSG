module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourNaturalPair
public import Theory.Representation.ScalarMultiplicity.Kernel
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.Representation.DihedralPlaneFour
public import Theory.SpecificGroups.SL2.BinaryDihedral
/-!
# The multiplicity action of the original Hermitian pair

The two natural four-spaces on P/U have scalar commutant F₄. The
commutator bound [R,I] ≤ O₂(R) therefore constructs a two-dimensional
F₄ action of I. Pure tensors preserve its full kernel, so it descends
faithfully to the original quotient I/O₂(I). Its action formula retains
the selected conjugator and the literal B₀/U inclusion as well as the
diagonal R/O₂(R) action. No invariant choice of the two copies is assumed.

Source: Aschbacher–Smith 8.2.8(3–5), printed pp.718–719,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic.Construction Normalizer.SmallOvergroups
public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G]

/-- Faithful multiplicity coordinates, with the original section, conjugator and quotient actions. -/
@[expose] def PairMultiplicityAction (R I V U : Subgroup G) (i : I) : Prop :=
  let W := Multiplicative (Fin 2 → E 1)
  let B := V ⊓ I.pCoreIn 2
  let Y := R ⊔ I
  ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
    ∃ hYU : Y ≤ normalizer (U : Set G),
      ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
        ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
          ∃ eB : (B ⧸ U.subgroupOf B) ≃* W,
            ∃ eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1),
              ∃ eP : W × W ≃* (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
                ∃ μ : Representation (E 1) (I ⧸ pCore 2 I) (Fin 2 → E 1),
                  let q := QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl)
                    (show B ≤ I.pCoreIn 2 from inf_le_right)
                  let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
                  Function.Injective μ.asGroupHom ∧
                  (∀ x y, eP (x,y) = q (eB.symm x) *
                    f (inclusion le_sup_right i⁻¹) (q (eB.symm y))) ∧
                  (∀ (r : R) x y, f (inclusion le_sup_left r) (eP (x,y)) =
                    eP (Matrix.SL2.naturalAction (E 1) (eR (QuotientGroup.mk' (pCore 2 R) r)) x,
                      Matrix.SL2.naturalAction (E 1) (eR (QuotientGroup.mk' (pCore 2 R) r)) y)) ∧
                  ∀ (a : I) (c : Fin 2 → E 1) (v : Fin 2 → E 1),
                    f (inclusion le_sup_right a)
                      (eP (Multiplicative.ofAdd (c 0 • v),Multiplicative.ofAdd (c 1 • v))) =
                    eP (Multiplicative.ofAdd (μ (QuotientGroup.mk' (pCore 2 I) a) c 0 • v),
                      Multiplicative.ofAdd (μ (QuotientGroup.mk' (pCore 2 I) a) c 1 • v))

/-- Commuting with the diagonal natural action constructs the full original quotient action on its multiplicity plane. -/
theorem pair_multiplicity_action (R I V U : Subgroup G) (i : I)
    (hp : PairProductAction R I V U) (hn : PairNaturalAction R I V U i)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2) : PairMultiplicityAction R I V U i := by
  obtain ⟨hYP,hYU,hUP,hBU,eB,eR,eP,heP,hR⟩ := hn
  let := hUP
  let := hBU
  obtain ⟨_,_,_,hEl,hcard,hker,hcore,hRker,hIker,_⟩ := hp
  let := hEl
  let W := Multiplicative (Fin 2 → E 1)
  let X := Fin 2 → (Fin 2 → E 1)
  let P := I.pCoreIn 2
  let Y := R ⊔ I
  let f := sectionAction Y P U hYP hYU
  let e : Multiplicative X ≃* (P ⧸ U.subgroupOf P) :=
    (LinearEquiv.finTwoArrow (E 1) (Fin 2 → E 1)).toAddEquiv.toMultiplicative.trans
      ((MulEquiv.prodMultiplicative _ _).trans eP)
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
  let σ : Representation (ZMod 2) SL(2,E 1) (Fin 2 → E 1) := {
    toFun g := (specialLinearNatural 2 g).toAddMonoidHom.toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (map_one (specialLinearNatural 2)) v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (map_mul (specialLinearNatural 2) g h) v }
  have hc (g : I) (d : SL(2,E 1)) (x : X) :
      ρ g (fun j => σ d (x j)) = fun j => σ d (ρ g x j) := by
    obtain ⟨r,hr⟩ := QuotientGroup.mk'_surjective (pCore 2 R) (eR.symm d)
    have hdr : eR (QuotientGroup.mk' (pCore 2 R) r) = d := by rw [hr,eR.apply_symm_apply]
    have hdiag (x : X) :
        e (Multiplicative.ofAdd (fun j => σ d (x j))) =
          f (inclusion le_sup_left r) (e (Multiplicative.ofAdd x)) := by
      change eP (Multiplicative.ofAdd (σ d (x 0)),Multiplicative.ofAdd (σ d (x 1))) =
        f (inclusion le_sup_left r) (eP (Multiplicative.ofAdd (x 0),Multiplicative.ofAdd (x 1)))
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
  obtain ⟨μ,hμ,hμker⟩ := ScalarMultiplicity.exists_multiplicity_kernel σ
    (fun l hl => SL2NaturalOffenders.centralizer_scalar l.toAddMonoidHom hl) ρ hc
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
  let ν : Representation (E 1) (I ⧸ pCore 2 I) (Fin 2 → E 1) :=
    (Units.coeHom (Module.End (E 1) (Fin 2 → E 1))).comp μq
  refine ⟨hYP,hYU,hUP,hBU,eB,eR,eP,ν,?_,heP,hR,?_⟩
  · intro x y hxy
    apply hi
    apply Units.ext
    have hh := congrArg (fun z : (Module.End (E 1) (Fin 2 → E 1))ˣ => z.val) hxy
    exact hh
  · intro g c v
    have hh := hρ g (fun j => c j • v)
    rw [hμ] at hh
    exact hh.symm

/-- The original parameter-one pair has precisely the cubic or quintic
quotient allowed by 8.2.8(3). The full multiplicity action is retained. -/
theorem selected_one_multiplicity_cases [Finite G]
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hp : PairProductAction R I V U) (hn : PairNaturalAction R I V U i)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2) :
    PairMultiplicityAction R I V U i ∧
      (Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
       Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) := by
  have h := pair_multiplicity_action R I V U i hp hn hcomm
  refine ⟨h,?_⟩
  obtain ⟨_,_,_,_,_,_,_,μ,hμ,_⟩ := h
  rcases s.models with ⟨hk,_⟩ | ⟨m,hm,hk,_⟩ | ⟨_,p,a,hp,ho,ha,⟨d⟩⟩
  · omega
  · omega
  · let ρ : Representation (E 1) (DihedralGroup (p^a)) (Fin 2 → E 1) :=
      μ.comp d.symm.toMonoidHom
    have hi : Function.Injective ρ.asGroupHom := by
      intro x y hxy
      apply d.symm.injective
      apply hμ
      apply Units.ext
      have hh := congrArg (fun z : (Module.End (E 1) (Fin 2 → E 1))ˣ => z.val) hxy
      exact hh
    have hF : Nat.card (E 1) = 4 := by rw [card_E]; norm_num
    rcases dihedral_prime_power_plane_four hF hp ho ha ρ hi with he | he
    · left
      have he' : Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 3) :=
        he ▸ (show Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup (p^a)) from ⟨d⟩)
      obtain ⟨d'⟩ := he'
      exact ⟨d'.trans Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two⟩
    · right
      exact he ▸ (show Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup (p^a)) from ⟨d⟩)
end
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
