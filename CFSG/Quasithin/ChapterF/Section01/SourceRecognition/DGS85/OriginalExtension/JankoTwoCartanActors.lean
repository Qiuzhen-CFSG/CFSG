module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoOuterCenter

public import Mathlib.Data.Fintype.Perm

/-!
# Cartan actors in the original Hall–Janko Borel

The reduced Sylow has trivial second coordinate under the constructed
S₃ × S₃ quotient: its elements have two-power order, whereas the reduced
second factor is cubic. An actor in the second quotient factor therefore
normalizes the same reduced Sylow. Since the local factor is normal in
its parabolic, the original F.1.1 Borel-normalizer identity puts that actor
in the whole original Borel.

An involution commuting with the fixed-point-free cubic has trivial first
coordinate. Its exact inversion relation forces the same for the reduced
cubic. Thus the actors already constructed lie in the original Borel, with
k in B₀ and x outside B₀, and still fix the entire original core center.
The actual orders 128 and 384 show that every cubic in B₀ generates a
complement to its same reduced Sylow. These are group and subgroup
statements, not quotient-only relations or order-based recognition.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.229–230, through
the choice of the Cartan generator and the outer Borel involution. The
remaining endpoint-generator relations, the order-12 product on p.231,
and Aut(J₂) parabolic equivalences are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
open SuzukiContainment GreenBook
open Sporadic.LeechRelated.J2.ExceptionalParabolics
local notation "S3" => Equiv.Perm (Fin 3)
local notation "C3" => Multiplicative (ZMod 3)
private theorem s3_involution_fixed :
    ∀ u w : S3,u^3=1 → w^2=1 → u*w=w*u → u=1 ∨ w=1 := by
  intro u w
  fin_cases u <;> fin_cases w <;> decide +kernel

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- An actor in the complementary quotient factor belongs to the original
whole Borel. The proof uses the actual reduced Sylow, not a conjugate. -/
theorem original_second_marked_actor_mem_borel
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (d : (parabolic L S j ⧸ pCore 2 (parabolic L S j)) ≃* (S3 × S3))
    (c : C3 →* S3) (hc : Function.Injective c)
    (hd : ∀ z,d (coreQuotientMap h j z)=
      ((reducedSecondQuotientEquiv j f z).1,c (reducedSecondQuotientEquiv j f z).2))
    (y : parabolic L S j)
    (hy : (d (QuotientGroup.mk' (pCore 2 (parabolic L S j)) y)).1=1) :
    (y : G) ∈ commonBorel L S := by
  let P := parabolic L S j
  let R := reducedSylow L S
  have hRP : R ≤ P := (reducedSylow_le h).trans (le_sup_right.trans le_sup_left)
  let T := R.subgroupOf P
  let v := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hv : Function.Surjective v := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : v.ker ≤ T := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
    intro z hz
    exact parabolic_core_le_reducedSylow h j (mem_map_of_mem P.subtype hz)
  have htv (t : P) (ht : t ∈ T) : (v t).2=1 := by
    have hcub : (v t).2 ∈ alternatingGroup (Fin 3) :=
      (original_second_quotient_reduced h j f d c hc hd t).mpr
        ((le_sup_right.trans le_sup_left : R ≤ parabolic L R j) ht)
    let z : R := ⟨t,ht⟩
    have hz : z^128=1 := by
      have hh := pow_card_eq_one' (x := z)
      rwa [reduced_sylow_card h i e] at hh
    have ht128 : t^128=1 := Subtype.ext (congrArg (fun z : R => (z : G)) hz)
    have hv128 : (v t).2^128=1 := by
      have hh := congrArg (fun w => (v w).2) ht128
      simpa using hh
    exact (show ∀ w : S3,w^128=1 → w ∈ alternatingGroup (Fin 3) → w=1 by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel) _ hv128 hcub
  have hcomm : v y ∈ centralizer (T.map v : Set (S3 × S3)) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨t,ht,rfl⟩
    apply Prod.ext
    · change (v t).1*(v y).1=(v y).1*(v t).1
      rw [show (v y).1=1 from hy,mul_one,one_mul]
    · change (v t).2*(v y).2=(v y).2*(v t).2
      rw [htv t ht,one_mul,mul_one]
  have hyn : y ∈ normalizer (T : Set P) := by
    have hh : y ∈ (normalizer (T.map v : Set (S3 × S3))).comap v :=
      Subgroup.centralizer_le_normalizer _ hcomm
    rwa [comap_normalizer_eq_of_surjective _ hv,comap_map_eq,sup_eq_left.mpr hk] at hh
  have hynG : (y : G) ∈ normalizer (R : Set G) := by
    rwa [←subgroupOf_normalizer_eq hRP] at hyn
  have hPL : P ≤ normalizer (L j : Set G) := by
    dsimp [P]
    rw [parabolic_eq_sup_commonBorel]
    exact sup_le (L j).le_normalizer (h.commonBorel_normalizes_local j)
  rw [h.commonBorel_eq_normalizer j]
  refine ⟨y.property,?_⟩
  rw [←reducedSylow_inf h j]
  apply mem_normalizer_iff.mpr
  intro t
  exact and_congr (mem_normalizer_iff.mp hynG t) (mem_normalizer_iff.mp (hPL y.property) t)

/-- The exact outer pair lies in the same original full Borel. The reduced
cubic belongs to the reduced Borel, and the involution leaves it. Both fix
the center of the unchanged second core. -/
theorem exists_original_borel_outer_cubic_relations
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    ∃ k x : parabolic L S j,
      orderOf k=3 ∧ (k : G) ∈ commonBorel L (reducedSylow L S) ∧
      x^2=1 ∧ (x : G) ∈ commonBorel L S ∧
      (x : G) ∉ commonBorel L (reducedSylow L S) ∧
      originalCubic h j f*k=k*originalCubic h j f ∧
      originalCubic h j f*x=x*originalCubic h j f ∧ x*k*x⁻¹=k⁻¹ ∧
      ∀ z ∈ (center (pCore 2 (parabolic L S j))).map (pCore 2 (parabolic L S j)).subtype,
        x*z=z*x ∧ k*z=z*k := by
  obtain ⟨k,x,hk,hkR,hx,hxR,hak,hax,hxk,hfix⟩ :=
    exists_original_outer_cubic_relations_fixing_core_center h i j e f hne
  let P := parabolic L S j
  let q := QuotientGroup.mk' (pCore 2 P)
  let a := originalCubic h j f
  obtain ⟨d,c,hci,hd⟩ := original_second_quotient_marked_of_ne h i j e f hne
  let v := d.toMonoidHom.comp q
  let u := (reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ (reducedCubic j f))).1
  have ha : v a=(u,1) := by
    have hh := hd (QuotientGroup.mk' _ (reducedCubic j f))
    rw [reducedCubic_second_coordinate,map_one] at hh
    have hm : coreQuotientMap h j (QuotientGroup.mk' _ (reducedCubic j f)) =
        q a := coreQuotientMap_mk h j (reducedCubic j f)
    rwa [hm] at hh
  have hu3 : u^3=1 := by
    have hh := congrArg (fun z => (v z).1) (originalCubic_cube h j f)
    change (v (a^3)).1=(v 1).1 at hh
    simpa [ha] using hh
  have hune : u≠1 := by
    intro hh
    have hv1 : v a=1 := by rw [ha,hh]; rfl
    have hq1 : q a=1 := d.injective (hv1.trans d.map_one.symm)
    have hacore : a ∈ pCore 2 P := (QuotientGroup.eq_one_iff _).mp hq1
    have ha1 := originalCubic_core_fixed h j f a hacore rfl
    have ho := originalCubic_order h j f
    change orderOf a=3 at ho
    rw [ha1,orderOf_one] at ho
    contradiction
  have hx2 : (v x).1^2=1 := by
    simpa using congrArg (fun z => (v z).1) hx
  have hxc : u*(v x).1=(v x).1*u := by
    have hh := congrArg (fun z => (v z).1) hax
    change (v (a*x)).1=(v (x*a)).1 at hh
    simpa [ha] using hh
  have hxfirst : (v x).1=1 :=
    (s3_involution_fixed u (v x).1 hu3 hx2 hxc).resolve_left hune
  have hk3 : k^3=1 := by simpa only [hk] using pow_orderOf_eq_one k
  have hvk3 : (v k).1^3=1 := by
    simpa using congrArg (fun z => (v z).1) hk3
  have hvkinv : (v k).1=(v k).1⁻¹ := by
    have hh := congrArg (fun z => (v z).1) hxk
    simpa only [map_mul,map_inv,Prod.fst_mul,Prod.fst_inv,hxfirst,one_mul,inv_one,mul_one] using hh
  have hkfirst : (v k).1=1 :=
    (show ∀ w : S3,w^3=1 → w=w⁻¹ → w=1 by decide +kernel) _ hvk3 hvkinv
  have hxB := original_second_marked_actor_mem_borel h i j e f d c hci hd x hxfirst
  have hkB := original_second_marked_actor_mem_borel h i j e f d c hci hd k hkfirst
  have hkB0 : (k : G) ∈ commonBorel L (reducedSylow L S) := by
    rw [←reduced_parabolic_inf_borel h j]
    exact ⟨hkR,hkB⟩
  exact ⟨k,x,hk,hkB0,hx,hxB,fun hh => hxR (commonBorel_le_parabolic j hh),
    hak,hax,hxk,hfix⟩

/-- Every cubic in the reduced full Borel is an actual Cartan complement to
its same reduced Sylow. The odd Borel factor is retained. -/
theorem reduced_borel_cubic_complement
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (b : commonBorel L (reducedSylow L S) ≃* HallJanko.j2Model.toMarking.B)
    (k : commonBorel L (reducedSylow L S)) (hk : orderOf k=3) :
    IsComplement' (zpowers k)
      ((reducedSylow L S).subgroupOf (commonBorel L (reducedSylow L S))) := by
  let := (reduced_hypothesis h).finite_commonBorel
  have hK : Nat.card (zpowers k)=3 := (Nat.card_zpowers k).trans hk
  have hS : Nat.card ((reducedSylow L S).subgroupOf (commonBorel L (reducedSylow L S)))=128 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (le_sup_right : reducedSylow L S ≤ commonBorel L (reducedSylow L S))).toEquiv).trans
        (reduced_sylow_card h i e)
  have hB : Nat.card (commonBorel L (reducedSylow L S))=384 :=
    (Nat.card_congr b.toEquiv).trans HallJanko.card_j2Model_B
  exact isComplement'_of_coprime (by rw [hK,hS,hB]) (by rw [hK,hS]; decide)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
