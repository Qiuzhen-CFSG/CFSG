module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars.Model
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupAction.IrreducibleSmallLinear
public import Theory.GroupTheory.CyclicNormalOddQuotient.CyclicImage

/-!
# Odd actors in the highest-root centralizer of PSL₃

An odd-primary subgroup centralizing the highest-root group embeds into the
cyclic diagonal part of that centralizer: its intersection with the unipotent
two-core is trivial. An odd subgroup in a marked Borel is therefore cyclic
if its full normalizer acts irreducibly on its Frattini quotient and the
ambient actor preserves the marked root group. The scalar character makes
the root action image cyclic; irreducibility kills that image, reducing to
the centralizer calculation.

The ambient actor need not normalize the whole marked PSL₃ subgroup. Only
its action on the actual root subgroup is used. This distinction is needed
in Aschbacher–Smith, proof of 13.1.12, printed p.875, where the root subgroup
is the center of O₂(X), preserved by N_G(X).
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.CartanActions.BorelQuotient Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree.RootScalars
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private def diagonalTorus : Fˣ →* PSL(3,F) := (torusMap F).comp
  { toFun := fun a => (a,a)
    map_one' := rfl
    map_mul' _ _ := rfl }

private def diagonalBorel : Fˣ →* borel F := (diagonalTorus F).codRestrict
  (borel F) (fun a => torus_le_borel F ⟨(a,a),rfl⟩)

private theorem centralizer_factorization (c : PSL(3,F))
    (hc : c ∈ centralizer (projectiveCenter F : Set PSL(3,F))) :
    ∃ a : Fˣ, ∃ u ∈ unipotent F, c = u * diagonalTorus F a := by
  obtain ⟨g,rfl⟩ := projection_surjective F c
  obtain ⟨hg,he⟩ := (mem_centralizer_projectiveCenter_iff F g).mp hc
  obtain ⟨d,u,hu,hgprod⟩ := borelSL_factorization F g hg
  have hu00 := ((mem_pointLocalSL_iff F u).mp hu.1).1
  have hu22 := ((mem_lineLocalSL_iff F u).mp hu.2).2.2
  have hd0 : g.val 0 0 = (d.1 : F) := by
    rw [hgprod, SpecialLinearGroup.coe_mul, torusSL_val, Matrix.mul_diagonal]
    simp [hu00]
  have hd2 : g.val 2 2 = (d.2 : F) := by
    rw [hgprod, SpecialLinearGroup.coe_mul, torusSL_val, Matrix.mul_diagonal]
    simp [hu22]
  have hd : d.1 = d.2 := Units.ext (hd0.symm.trans (he.trans hd2))
  refine ⟨d.1,projection F u,mem_map_of_mem _ hu,?_⟩
  rw [hgprod,map_mul]
  change projection F u * torusMap F d = projection F u * torusMap F (d.1,d.1)
  congr 2
  exact Prod.ext rfl hd.symm

/-- Every odd-primary subgroup centralizing the highest-root group is cyclic. -/
theorem isCyclic_of_odd_pGroup_le_root_centralizer {n p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = 2 ^ n) (ho : Odd p)
    (P : Subgroup PSL(3,F)) (hP : IsPGroup p P)
    (hc : P ≤ centralizer (projectiveCenter F : Set PSL(3,F))) : IsCyclic P := by
  let B := borel F
  let q := QuotientGroup.mk' (pCore 2 B)
  have hPB : P ≤ B := hc.trans (le_sup_left.trans (centralizer_sup_complementTorus F).le)
  let j : P →* B := inclusion hPB
  let f := q.comp j
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxQ : j x ∈ pCore 2 B := (QuotientGroup.eq_one_iff _).mp hx
    have hxP : j x ∈ P.subgroupOf B := x.property
    have hd : Disjoint (pCore 2 B) (P.subgroupOf B) :=
      pCore_isPGroup.disjoint_of_coprime hP.comap_subtype
      (Nat.coprime_two_left.mpr ho)
    have hj1 : j x = 1 := hd.le_bot ⟨hxQ,hxP⟩
    change x = 1
    apply Subtype.ext
    exact congrArg (fun b : B => (b : PSL(3,F))) hj1
  let D := (q.comp (diagonalBorel F)).range
  let : IsCyclic D := isCyclic_of_surjective (q.comp (diagonalBorel F)).rangeRestrict
    (q.comp (diagonalBorel F)).rangeRestrict_surjective
  have hfd : ∀ x, f x ∈ D := by
    intro x
    obtain ⟨a,u,hu,he⟩ := centralizer_factorization F x (hc x.property)
    let uB : B := ⟨u,unipotent_le_borel F hu⟩
    have huQ : q uB = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [twoCore_eq F hF]
      exact hu
    refine ⟨a,?_⟩
    have hj : j x = uB * diagonalBorel F a := Subtype.ext he
    change q (diagonalBorel F a) = q (j x)
    rw [hj,map_mul,huQ,one_mul]
  exact isCyclic_of_injective (f.codRestrict D hfd)
    (fun x y he => hi (congrArg Subtype.val he))

/-- A marked Borel actor with irreducible Frattini normalizer action is cyclic
when its ambient normalizer preserves the actual highest-root subgroup. -/
theorem isCyclic_of_irreducible_borel_actor {G : Type*} [Group G] [Finite G]
    {n p : ℕ} [Fact p.Prime] (hF : Nat.card F = 2 ^ n) (ho : Odd p)
    (M K P R : Subgroup G) (hPM : P ≤ M) (hPK : P ≤ K) (hRK : R ≤ K)
    (hMR : M ≤ normalizer (R : Set G))
    (e : K ≃* PSL(3,F))
    (hB : (P.subgroupOf K).map e.toMonoidHom ≤ borel F)
    (hR : (R.subgroupOf K).map e.toMonoidHom = projectiveCenter F)
    (hP : IsPGroup p P) (hirr : IsNormalizerFrattiniIrreducible (P.subgroupOf M)) :
    IsCyclic P := by
  by_contra hnc
  let PM := P.subgroupOf M
  let ep : PM ≃* P := subgroupOfEquivOfLe hPM
  have hncM : ¬ IsCyclic PM := fun hh => hnc (ep.isCyclic.mp hh)
  let i : PM →* PSL(3,F) := e.toMonoidHom.comp ((inclusion hPK).comp ep.toMonoidHom)
  have hi : Function.Injective i := e.injective.comp ((inclusion_injective hPK).comp ep.injective)
  have hiB (x : PM) : i x ∈ borel F := hB ⟨⟨ep x,hPK (ep x).property⟩,(ep x).property,rfl⟩
  let j : PM →* borel F := i.codRestrict (borel F) hiB
  let d : PM →* Fˣ := (borelCharacter F).comp j
  let rho : M →* MulAut R := R.normalizerMonoidHom.comp (inclusion hMR)
  let f := rho.comp PM.subtype
  have hk : d.ker ≤ f.ker := by
    intro x hx
    have hx1 : borelCharacter F (j x) = 1 := hx
    apply MulEquiv.ext
    intro r
    apply Subtype.ext
    have hr : e ⟨r,hRK r.property⟩ ∈ projectiveCenter F :=
      hR ▸ mem_map_of_mem _ r.property
    rw [← root_range F] at hr
    obtain ⟨a,ha⟩ := hr
    have hc := borel_conjugation F (j x) a.toAdd
    rw [hx1,Units.val_one,one_mul,ofAdd_toAdd,ha] at hc
    have heq : e (⟨(ep x : G) * (r : G) * (ep x : G)⁻¹,
      K.mul_mem (K.mul_mem (hPK (ep x).property) (hRK r.property))
        (K.inv_mem (hPK (ep x).property))⟩ : K) = e ⟨r,hRK r.property⟩ := by
      change e ((⟨ep x,hPK (ep x).property⟩ : K) * ⟨r,hRK r.property⟩ *
        (⟨ep x,hPK (ep x).property⟩ : K)⁻¹) = _
      rw [map_mul,map_mul,map_inv]
      exact hc
    exact congrArg (fun k : K => (k : G)) (e.injective heq)
  have hfcyc : IsCyclic f.range :=
    Theory.GroupTheory.isCyclic_range_of_ker_le_cyclic d f hk
  have hf1 := hirr.comp_eq_one_of_cyclic_range hncM rho hfcyc
  have hic : i.range ≤ centralizer (projectiveCenter F : Set PSL(3,F)) := by
    rintro y ⟨x,rfl⟩
    rw [mem_centralizer_iff]
    intro z hz
    rw [← hR] at hz
    obtain ⟨r,hr,rfl⟩ := hz
    have hh := congrArg (fun a : MulAut R => ((a ⟨(r : K),hr⟩ : R) : G))
      (DFunLike.congr_fun hf1 x)
    change (ep x : G) * (r : G) * (ep x : G)⁻¹ = (r : G) at hh
    have hcomm : (ep x : G) * (r : G) = (r : G) * (ep x : G) :=
      mul_inv_eq_iff_eq_mul.mp hh
    have hcK : (⟨ep x,hPK (ep x).property⟩ : K) * r =
        r * (⟨ep x,hPK (ep x).property⟩ : K) := Subtype.ext hcomm
    change e r * e (⟨ep x,hPK (ep x).property⟩ : K) =
      e (⟨ep x,hPK (ep x).property⟩ : K) * e r
    simpa only [map_mul] using (congrArg e hcK).symm
  have hip : IsPGroup p i.range :=
    (hP.of_equiv ep.symm).of_surjective i.rangeRestrict i.rangeRestrict_surjective
  let : IsCyclic i.range := isCyclic_of_odd_pGroup_le_root_centralizer F hF ho i.range hip hic
  exact hncM (isCyclic_of_injective i.rangeRestrict (fun x y h => hi (congrArg Subtype.val h)))

end Matrix.PSL3.LinearThree.RootScalars
