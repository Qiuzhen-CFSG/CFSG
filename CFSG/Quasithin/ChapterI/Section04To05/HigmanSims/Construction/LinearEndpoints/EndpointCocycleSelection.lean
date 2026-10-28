module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.OppositeRadicalMarking
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.NormalizerCubicCentralizer
public import Theory.Representation.SL2FourNaturalExtensions.CubicNormalizedCocycles
public import Theory.Representation.FirstCohomologySemidirect
public import Theory.GroupTheory.CosetWordCertificate
import Mathlib.Tactic.Group

/-!
# Physical endpoint lift selection fixing the cubic normalizer

All four natural cocycle classes act on the original endpoint, fixing its
complete elementary kernel and every original actor normalizing the prescribed
cubic. The action changes actual lifts, not their coordinate marking. The
explicit displacement retains the original quotient and kernel coordinates.
No extension to the hexad group or the full linear group is asserted.
-/

public noncomputable section
open Subgroup Theory.GroupTheory SemidirectProduct
namespace CFSG.Quasithin.HigmanSims
open Representation Representation.OneCohomology Representation.SL2FourNatural
open Representation.SL2FourNaturalExtensions
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]

private theorem fixes_cubic_normalizer {D H : Type*} [Group D] [Group H]
    (q : D →* H) (α : MulAut D) (hq : ∀ g, q (α g)=q g)
    (t : D) (ht : α t=t)
    (hct : ∀ a : q.ker, Commute (a:D) t → a=1)
    (g : D) (hg : g∈normalizer (zpowers t:Set D)) : α g=g := by
  have hfix (x : D) (hx : x∈zpowers t) : α x=x := by
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
    rw [map_zpow,ht]
  have he := hfix (g*t*g⁻¹) ((mem_normalizer_iff.mp hg t).mp (mem_zpowers t))
  rw [map_mul,map_mul,map_inv,ht] at he
  let a : q.ker := ⟨g⁻¹*α g,by simp only [MonoidHom.mem_ker,map_mul,map_inv,hq,inv_mul_cancel]⟩
  have ha : Commute (a:D) t := by
    change g⁻¹*α g*t=t*(g⁻¹*α g)
    calc
      _ = g⁻¹*(α g*t*(α g)⁻¹)*α g := by group
      _ = g⁻¹*(g*t*g⁻¹)*α g := by rw [he]
      _ = _ := by group
  have hz := congrArg Subtype.val (hct a ha)
  exact (inv_mul_eq_one.mp hz).symm

/-- Four distinct automorphisms of the original endpoint realize the four
natural displacement classes while fixing its full kernel and full cubic
normalizer. The formula changes actual endpoint elements in the original group. -/
theorem NaturalEndpointData.exists_cubic_normalized_endpoint_lifts
    (d : NaturalEndpointData A) (t : G) (ht : t∈d.carrier) (ht3 : orderOf t=3) :
    ∃ α : F → MulAut d.carrier, Function.Injective α ∧
      (∀ k g, d.quotient (α k g)=d.quotient g) ∧
      (∀ k (a : A), α k (inclusion d.kernel_le a)=inclusion d.kernel_le a) ∧
      (∀ k g, α k g = inclusion d.kernel_le
        (d.coordinates.symm (Multiplicative.ofAdd
          ((cubicCocycle (d.quotient ⟨t,ht⟩) k).val (d.quotient g)))) * g) ∧
      (∀ k, α k ⟨t,ht⟩=⟨t,ht⟩) ∧
      (∀ k g, g∈normalizer (zpowers (⟨t,ht⟩:d.carrier):Set d.carrier) → α k g=g) ∧
      (∀ k (P : Subgroup d.carrier), A.subgroupOf d.carrier≤P → P.map (α k).toMonoidHom=P) := by
  obtain ⟨f,hfq,hfk,_,_⟩ := d.exists_affine_marking
  let T : d.carrier := ⟨t,ht⟩
  let δ (k : F) := cubicCocycle (d.quotient T) k
  let β (k : F) : MulAut (Matrix.SL2.Affine F) :=
    splitCocycleAut naturalCocycleRep (Matrix.SL2.naturalAction F) (fun _ _ => rfl) (δ k)
  let α (k : F) : MulAut d.carrier := f.trans ((β k).trans f.symm)
  have hα (k : F) (g : d.carrier) : f (α k g)=β k (f g) := f.apply_symm_apply _
  have hq (k : F) (g : d.carrier) : d.quotient (α k g)=d.quotient g := by
    rw [←hfq, hα]
    exact hfq g
  have hform (k : F) (g : d.carrier) : α k g = inclusion d.kernel_le
      (d.coordinates.symm (Multiplicative.ofAdd ((δ k).val (d.quotient g)))) * g := by
    apply f.injective
    rw [hα,map_mul,hfk,d.coordinates.apply_symm_apply]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change (f g).left.toAdd+(δ k).val (f g).right =
        (δ k).val (d.quotient g)+(Matrix.SL2.naturalAction F 1 (f g).left).toAdd
      rw [map_one,hfq]
      exact add_comm _ _
    · change (f g).right=1*(f g).right
      exact (one_mul _).symm
  have hker (k : F) (a : A) : α k (inclusion d.kernel_le a)=inclusion d.kernel_le a := by
    have hz : (δ k).val 1=0 := by
      have hh := (δ k).property 1 1
      simpa using hh.symm
    have hqa : d.quotient (inclusion d.kernel_le a)=1 := by
      change inclusion d.kernel_le a∈d.quotient.ker
      rw [d.quotient_kernel]
      exact a.property
    rw [hform,hqa,hz]
    simp
  have hT3 : (d.quotient T)^3=1 := by
    rw [←map_pow]
    have hh : T^3=1 := by
      have horder : orderOf T=3 := (orderOf_coe T).symm.trans ht3
      rw [←horder,pow_orderOf_eq_one]
    rw [hh,map_one]
  have hT (k : F) : α k T=T := by
    rw [hform,show (δ k).val (d.quotient T)=0 from cubicCocycle_at _ hT3 k]
    simp
  have hct (a : d.quotient.ker) (ha : Commute (a:d.carrier) T) : a=1 := by
    have haA : ((a:d.carrier):G)∈A :=
      show (a:d.carrier)∈A.subgroupOf d.carrier from d.quotient_kernel ▸ a.property
    have he : ((a:d.carrier):G)∈centralizer ({t}:Set G) :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val ha.eq)
    have hz : ((a:d.carrier):G)∈(⊥:Subgroup G) :=
      d.cubic_radical_centralizer t ht ht3 ▸ (show ((a:d.carrier):G)∈
        A⊓centralizer ({t}:Set G) from ⟨haA,he⟩)
    exact Subtype.ext (Subtype.ext (mem_bot.mp hz))
  refine ⟨α,?_,hq,hker,hform,hT,fun k => fixes_cubic_normalizer d.quotient
    (α k) (hq k) T (hT k) hct,?_⟩
  · intro k l he
    apply cubicCocycle_injective (d.quotient T)
    apply Subtype.ext
    funext x
    obtain ⟨g,rfl⟩ := d.quotient_surjective x
    have hh := congrArg (fun a : MulAut d.carrier => (f (a g)).left.toAdd) he
    rw [hα,hα] at hh
    change (f g).left.toAdd+(δ k).val (f g).right =
      (f g).left.toAdd+(δ l).val (f g).right at hh
    simpa only [hfq] using add_left_cancel hh
  · intro k P hP
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      change α k g∈P
      rw [hform]
      exact P.mul_mem (hP (d.coordinates.symm _).property) hg
    · intro g hg
      refine ⟨(α k).symm g,?_,(α k).apply_symm_apply g⟩
      have hh := hform k ((α k).symm g)
      rw [(α k).apply_symm_apply] at hh
      have hd : inclusion d.kernel_le (d.coordinates.symm
          (Multiplicative.ofAdd ((δ k).val (d.quotient ((α k).symm g)))))∈P :=
        hP (d.coordinates.symm _).property
      rw [hh] at hg
      exact (P.mul_mem_cancel_left hd).mp hg

private theorem eval_automorphism {D I : Type*} [Group D] (α : MulAut D)
    (p : I → D) (w : CosetWordCertificate.Word I) :
    CosetWordCertificate.eval (fun i => α (p i)) w=α (CosetWordCertificate.eval p w) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [CosetWordCertificate.eval_cons,CosetWordCertificate.eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

/-- Every generating pair in the actual endpoint has four distinct physical
replacements with the same quotient values and the same reflection and torus
words. Both named actors are fixed as elements, not merely conjugacy classes. -/
theorem NaturalEndpointData.exists_cubic_fixed_generating_pairs
    (d : NaturalEndpointData A) (t : G) (ht : t∈d.carrier) (ht3 : orderOf t=3)
    (pair : Fin 2 → d.carrier) (hgen : closure (Set.range pair)=⊤)
    (r : d.carrier) (hr : r∈normalizer (zpowers (⟨t,ht⟩:d.carrier):Set d.carrier))
    (wr wt : CosetWordCertificate.Word (Fin 2))
    (hwr : CosetWordCertificate.eval pair wr=r)
    (hwt : zpowers (CosetWordCertificate.eval pair wt)=zpowers (⟨t,ht⟩:d.carrier)) :
    ∃ pairs : F → (Fin 2 → d.carrier), Function.Injective pairs ∧
      (∀ k, closure (Set.range (pairs k))=⊤) ∧
      (∀ k i, d.quotient (pairs k i)=d.quotient (pair i)) ∧
      (∀ k, CosetWordCertificate.eval (pairs k) wr=r) ∧
      (∀ k, CosetWordCertificate.eval (pairs k) wt=CosetWordCertificate.eval pair wt) ∧
      (∀ k i, pairs k i = inclusion d.kernel_le
        (d.coordinates.symm (Multiplicative.ofAdd
          ((cubicCocycle (d.quotient ⟨t,ht⟩) k).val (d.quotient (pair i))))) * pair i) := by
  obtain ⟨α,hi,hq,_,hform,_,hN,_⟩ := d.exists_cubic_normalized_endpoint_lifts t ht ht3
  let pairs (k : F) (i : Fin 2) := α k (pair i)
  have hTN : CosetWordCertificate.eval pair wt∈
      normalizer (zpowers (⟨t,ht⟩:d.carrier):Set d.carrier) := by
    apply (zpowers (⟨t,ht⟩:d.carrier)).le_normalizer
    rw [←hwt]
    exact mem_zpowers _
  refine ⟨pairs,?_,?_,fun k i => hq k (pair i),?_,?_,fun k i => hform k (pair i)⟩
  · intro k l hh
    apply hi
    apply MulEquiv.toMonoidHom_injective
    apply MonoidHom.eq_of_eqOn_dense hgen
    rintro _ ⟨i,rfl⟩
    exact congrFun hh i
  · intro k
    have hrange : Set.range (pairs k)=(α k) '' Set.range pair := by
      ext g
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨pair i,⟨i,rfl⟩,rfl⟩
      · rintro ⟨_,⟨i,rfl⟩,rfl⟩
        exact ⟨i,rfl⟩
    rw [hrange]
    change closure ((α k).toMonoidHom '' Set.range pair)=⊤
    rw [←MonoidHom.map_closure,hgen]
    rw [←MonoidHom.range_eq_map]
    exact (MonoidHom.range_eq_top).mpr (α k).surjective
  · intro k
    change CosetWordCertificate.eval (fun i => α k (pair i)) wr=r
    rw [eval_automorphism,hwr,hN k r hr]
  · intro k
    change CosetWordCertificate.eval (fun i => α k (pair i)) wt=_
    rw [eval_automorphism,hN k _ hTN]

end CFSG.Quasithin.HigmanSims
