module

public import Theory.SpecificGroups.PSL3.SmallCompletion.FirstReflectionScalarOrbit
public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.MarkedTransport
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Physical scalar choices of the original full linear generators

A scalar on the first endpoint radical extends across the entire original
linear group. It fixes the original first reflection and cubic actor,
preserves both endpoint groups and their full two-cores, and supplies an
actual new generating pair and exterior cycle satisfying all thirteen linear
relations. The second reflection is allowed to change. No extension across
the hexad group, or vanishing of a mixed hexad word, is assumed or concluded.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Subgroup.CosetWordCertificate
namespace CFSG.Quasithin.HigmanSims
open Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion
local notation "F" => Matrix.PSL3Four.F
local notation "PSL" => Matrix.PSL3Four.PSL
local notation "Mark" => Matrix.PSL3Four.MathieuAmalgamMarking.pair
variable {G : Type*} [Group G]

/-- Every radical scalar gives new actual linear generators, retaining the
original first reflection, cubic, both endpoints and both complete kernels.
The transformed marking witnesses extension across the same full linear group. -/
theorem exists_original_full_linear_scalar_generators
    (P Q L : Subgroup G) (hPL : P≤L) (hQL : Q≤L)
    (e : L≃*PSL)
    (hP : (P.subgroupOf L).map e.toMonoidHom=pointParabolic F)
    (hQ : (Q.subgroupOf L).map e.toMonoidHom=lineParabolic F)
    (r t ell : G) (hr : r∈L) (ht : t∈P) (hell : ell∈L)
    (her : e ⟨r,hr⟩=reflection F false)
    (heell : e ⟨ell,hell⟩=Matrix.PSL3Four.MathieuAmalgamMarking.cycle)
    (ht3 : orderOf t=3) (htell : Commute t ell) (k : Fˣ) :
    ∃ (α : MulAut L) (e' : L≃*PSL),
      (∀ g, e (α g)=firstReflectionScalarActor F k (e g)) ∧
      (∀ g, e' (α g)=e g) ∧
      α ⟨r,hr⟩=⟨r,hr⟩ ∧ α ⟨t,hPL ht⟩=⟨t,hPL ht⟩ ∧
      (P.subgroupOf L).map α.toMonoidHom=P.subgroupOf L ∧
      (Q.subgroupOf L).map α.toMonoidHom=Q.subgroupOf L ∧
      ((P.pCoreIn 2).subgroupOf L).map α.toMonoidHom=(P.pCoreIn 2).subgroupOf L ∧
      ((Q.pCoreIn 2).subgroupOf L).map α.toMonoidHom=(Q.pCoreIn 2).subgroupOf L ∧
      (P.subgroupOf L).map e'.toMonoidHom=pointParabolic F ∧
      (Q.subgroupOf L).map e'.toMonoidHom=lineParabolic F ∧
      orderOf (α ⟨ell,hell⟩:G)=3 ∧
      Commute t (α ⟨ell,hell⟩:G) ∧
      r*(α ⟨ell,hell⟩:G)*r⁻¹=(α ⟨ell,hell⟩:G)⁻¹ ∧
      ∃ pair : Fin 2→G,
        closure (Set.range pair)=P ∧ (∀ i,pair i∈P) ∧
        (∀ i,pair i=(α (e.symm (Mark i)):G)) ∧
        eval pair Matrix.PSL3Four.MathieuAmalgamMarking.reflectionWord=r ∧
        zpowers (eval pair Matrix.PSL3Four.MathieuAmalgamMarking.torusWord)=zpowers t ∧
        ∀ (n : G) (i : Fin 13),
          eval ![pair 0,pair 1,(α ⟨ell,hell⟩:G),n]
            (Theory.SpecificGroups.MathieuAmalgamCompletion.relator ⟨i.val,by omega⟩)=1 := by
  obtain ⟨α,hα,hrfix,_,hαP,hαQ,hαA,hαB⟩ :=
    exists_original_first_reflection_scalar_actor F e (P.subgroupOf L) (Q.subgroupOf L) hP hQ k
  let T : L := ⟨t,hPL ht⟩
  let E : L := ⟨ell,hell⟩
  have htc : Commute (e T) Matrix.PSL3Four.MathieuAmalgamMarking.cycle := by
    rw [←heell]
    exact (show Commute T E from Subtype.ext htell.eq).map e.toMonoidHom
  have htP : e T∈pointParabolic F := hP ▸ mem_map_of_mem e.toMonoidHom ht
  have htT : e T∈Matrix.PSL3.CartanActions.torus F := by
    apply point_cycle_centralizer_le_torus F _ htP
    rwa [←Matrix.PSL3Four.MathieuAmalgamMarking.cycle_eq_reflections]
  have hαt : α T=T := by
    apply e.injective
    rw [hα]
    exact firstReflectionScalarActor_fixes_full_torus F k (e T) htT
  have hαr : α (⟨r,hr⟩:L)=⟨r,hr⟩ := hrfix _ her
  let e' : L≃*PSL := α.symm.trans e
  have hmark (g : L) : e' (α g)=e g := by
    change e (α.symm (α g))=e g
    rw [α.symm_apply_apply]
  have he'P : (P.subgroupOf L).map e'.toMonoidHom=pointParabolic F := by
    calc
      _ = ((P.subgroupOf L).map α.toMonoidHom).map e'.toMonoidHom :=
        congrArg (Subgroup.map e'.toMonoidHom) hαP.symm
      _ = (P.subgroupOf L).map e.toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        exact MonoidHom.ext hmark
      _ = _ := hP
  have he'Q : (Q.subgroupOf L).map e'.toMonoidHom=lineParabolic F := by
    calc
      _ = ((Q.subgroupOf L).map α.toMonoidHom).map e'.toMonoidHom :=
        congrArg (Subgroup.map e'.toMonoidHom) hαQ.symm
      _ = (Q.subgroupOf L).map e.toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        exact MonoidHom.ext hmark
      _ = _ := hQ
  have he'r : e' ⟨r,hr⟩=Matrix.PSL3Four.MathieuAmalgamMarking.reflection := by
    rw [←hαr,hmark,her,Matrix.PSL3Four.MathieuAmalgamMarking.reflection_eq_standard]
  have hnewcomm : Commute t (α E:G) := by
    have hh := (show Commute T E from Subtype.ext htell.eq).map α.toMonoidHom
    change Commute (α T) (α E) at hh
    rw [hαt] at hh
    exact hh.map L.subtype
  have hneworder : orderOf (α E:G)=3 := by
    rw [orderOf_coe,α.orderOf_eq]
    rw [←e.orderOf_eq E,heell]
    exact Matrix.PSL3Four.MathieuAmalgamMarking.canonical_orders.2.2
  have hnewinv : r*(α E:G)*r⁻¹=(α E:G)⁻¹ := by
    have hh : (⟨r,hr⟩:L)*(α E)*(⟨r,hr⟩:L)⁻¹=(α E)⁻¹ := by
      apply e'.injective
      rw [map_mul,map_mul,map_inv,map_inv,he'r,hmark,heell]
      exact Matrix.PSL3Four.MathieuAmalgamMarking.canonical_cubic_relations.2.2
    exact congrArg Subtype.val hh
  obtain ⟨pair,hgen,hmem,hpair,hwr,hwt,hrels⟩ :=
    Matrix.PSL3Four.MathieuAmalgamMarking.exists_original_marked_linear_relators
      P L hPL e' he'P (α E:G) r t (α E).property hr ht
      ((hmark E).trans heell) he'r ht3 hnewcomm
  refine ⟨α,e',hα,hmark,hαr,hαt,hαP,hαQ,?_,?_,he'P,he'Q,hneworder,hnewcomm,hnewinv,
    pair,hgen,hmem,?_,hwr,hwt,hrels⟩
  · simpa only [pCoreIn_subgroupOf 2 P L hPL] using hαA
  · simpa only [pCoreIn_subgroupOf 2 Q L hQL] using hαB
  · intro i
    rw [hpair]
    rfl

end CFSG.Quasithin.HigmanSims
