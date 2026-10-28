module
public import Theory.GroupTheory.DisjointCommutingProduct.SolvableProjections
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Sylow control of projected cubic supplements

A Sylow two-subgroup preserving two commuting factors and a two-perfect
subgroup also preserves the two projections of its two-core. Their join
is a two-group, so Sylow maximality puts it inside the original Sylow.
If an actor normalizes the cubic supplement and is covered by its two
projections, it normalizes this larger two-group. Recovering the original
subgroup as the two-residual of that join proves its normalization.

For a cubic with faithful projections to two cubic factors, cardinality
makes each projection surjective, supplying the required cover through
the actual multiplication maps. This is the terminal projection argument
in Aschbacher–Smith 14.7.32, printed p.1059.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
open Subgroup.MultiplicationProjections
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_projections
    (A C H R : Subgroup G) (e : A × C ≃* ↥(A ⊔ C))
    (hR : R ≤ A ⊔ C) (hn : H ≤ normalizer (R : Set G)) :
    leftAmbient e H ≤ normalizer (leftAmbient e R : Set G) ∧
      rightAmbient e H ≤ normalizer (rightAmbient e R : Set G) := by
  have hnN : H.subgroupOf (A ⊔ C) ≤ normalizer (R.subgroupOf (A ⊔ C) : Set ↥(A ⊔ C)) := by
    rw [←subgroupOf_normalizer_eq hR]
    exact comap_mono hn
  constructor
  · exact (map_mono ((map_mono hnN).trans ((R.subgroupOf (A ⊔ C)).le_normalizer_map _))).trans
      ((left e R).le_normalizer_map A.subtype)
  · exact (map_mono ((map_mono hnN).trans ((R.subgroupOf (A ⊔ C)).le_normalizer_map _))).trans
      ((right e R).le_normalizer_map C.subtype)

omit [Finite G] in
/-- A split actor preserving a cubic supplement preserves the two-perfect
subgroup, once an ambient Sylow normalizes the subgroup and both factors. -/
theorem normalizes_of_projected_cubic_supplement
    (S : Sylow 2 G) (A C L B P : Subgroup G)
    (e : A × C ≃* ↥(A ⊔ C))
    (he : ∀ a c, (e (a,c) : G) = (a : G) * (c : G))
    (hc : A ≤ centralizer (C : Set G))
    (hL : L ≤ A ⊔ C) (hp : IsPPerfect 2 L)
    (hgen : B ⊔ L.pCoreIn 2 = L)
    (hSA : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hSC : (S : Subgroup G) ≤ normalizer (C : Set G))
    (hSL : (S : Subgroup G) ≤ normalizer (L : Set G))
    (hPB : P ≤ normalizer (B : Set G))
    (hP : P ≤ leftAmbient e B ⊔ rightAmbient e B) :
    P ≤ normalizer (L : Set G) := by
  let R := L.pCoreIn 2
  let Q := leftAmbient e R ⊔ rightAmbient e R
  have hRL : R ≤ L := pCoreIn_le 2 L
  have hRN : R ≤ A ⊔ C := hRL.trans hL
  have hBL : B ≤ L := le_sup_left.trans_eq hgen
  have hBR : B ≤ normalizer (R : Set G) := hBL.trans
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hSR : (S : Subgroup G) ≤ normalizer (R : Set G) :=
    hSL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQp : IsPGroup 2 Q := by
    have h1 : IsPGroup 2 (leftAmbient e R) :=
      (((isPGroup_pCoreIn 2 L).comap_subtype).map _).map _
    have h2 : IsPGroup 2 (rightAmbient e R) :=
      (((isPGroup_pCoreIn 2 L).comap_subtype).map _).map _
    apply h1.to_sup_of_normal_right' h2
    exact (map_subtype_le _).trans (hc.trans ((centralizer_le (map_subtype_le _)).trans
      (centralizer_le_normalizer _)))
  have hSQ : (S : Subgroup G) ≤ normalizer (Q : Set G) := by
    intro s hs
    obtain ⟨h1,h2⟩ := map_eq_self_of_fixed_factors e he hc R (MulAut.conj s)
      (mem_normalizer_iff_map_conj_eq.mp (hSR hs))
      (mem_normalizer_iff_map_conj_eq.mp (hSA hs))
      (mem_normalizer_iff_map_conj_eq.mp (hSC hs))
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [show Q = leftAmbient e R ⊔ rightAmbient e R from rfl,Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) h1 h2
  have hQS : Q ≤ S := hQp.le_sylow_of_normalized S hSQ
  have hRQ : R ≤ Q := le_sup_projections e he R R hRN le_rfl
  have hPQ : P ≤ normalizer (Q : Set G) := by
    obtain ⟨h1,h2⟩ := normalizes_projections A C B R e hRN hBR
    have h12 : leftAmbient e B ≤ normalizer (rightAmbient e R : Set G) :=
      (map_subtype_le _).trans (hc.trans ((centralizer_le (map_subtype_le _)).trans
        (centralizer_le_normalizer _)))
    have h21 : rightAmbient e B ≤ normalizer (leftAmbient e R : Set G) :=
      (map_subtype_le _).trans ((le_centralizer_iff.mp hc).trans
        ((centralizer_le (map_subtype_le _)).trans (centralizer_le_normalizer _)))
    apply hP.trans
    exact sup_le
      ((le_inf h1 h12).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
      ((le_inf h21 h2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
  have hjoin : L ⊔ Q = B ⊔ Q := by
    rw [←hgen,sup_assoc,sup_eq_right.mpr hRQ]
  have hPN : P ≤ normalizer ((L ⊔ Q : Subgroup G) : Set G) := by
    rw [hjoin]
    exact (le_inf hPB hPQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hres := embedded_pResidual_join_pGroup L Q hp hQp (hQS.trans hSL)
  have hn := hPN.trans (normalizer_le_normalizer_characteristic_image
    (L ⊔ Q) (pResidual 2 (L ⊔ Q : Subgroup G)))
  rwa [hres] at hn

/-- Faithful projections of a cubic onto two cubic factors fill both
factors, using their literal multiplication coordinates. -/
theorem le_sup_projections_of_faithful_cubic_split
    (A C P B : Subgroup G) (e : A × C ≃* ↥(A ⊔ C))
    (he : ∀ a c, (e (a,c) : G) = (a : G) * (c : G))
    (hc : A ≤ centralizer (C : Set G))
    (hs : P = (P ⊓ A) ⊔ (P ⊓ C))
    (hB : Nat.card B = 3) (hA : Nat.card (P ⊓ A : Subgroup G) = 3)
    (hC : Nat.card (P ⊓ C : Subgroup G) = 3) (hBP : B ≤ P)
    (eP : (P ⊓ A : Subgroup G) × (P ⊓ C : Subgroup G) ≃* P)
    (heP : ∀ a c, (eP (a,c) : G) = (a : G) * (c : G))
    (h1 : Function.Injective ((MonoidHom.fst _ _).comp
      (eP.symm.toMonoidHom.comp (inclusion hBP))))
    (h2 : Function.Injective ((MonoidHom.snd _ _).comp
      (eP.symm.toMonoidHom.comp (inclusion hBP)))) :
    P ≤ leftAmbient e B ⊔ rightAmbient e B := by
  let f := eP.symm.toMonoidHom.comp (inclusion hBP)
  have hf (b : B) : (b : G) = ((f b).1 : G) * ((f b).2 : G) := by
    have hh := heP (f b).1 (f b).2
    change (eP (eP.symm (inclusion hBP b)) : G) = _ at hh
    rwa [eP.apply_symm_apply] at hh
  have hf1 : Function.Surjective ((MonoidHom.fst _ _).comp f) :=
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨h1,hB.trans hA.symm⟩).2
  have hf2 : Function.Surjective ((MonoidHom.snd _ _).comp f) :=
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨h2,hB.trans hC.symm⟩).2
  rw [hs]
  apply sup_le
  · intro a ha
    apply mem_sup_left
    obtain ⟨b,hb⟩ := hf1 ⟨a,ha⟩
    have hbval : ((f b).1 : G) = a := congrArg (fun z : ↥(P ⊓ A) => (z : G)) hb
    apply (mem_leftAmbient_iff e he B a).mpr
    refine ⟨ha.2,(f b).2,(f b).2.property.2,?_⟩
    rw [←hbval,←hf]
    exact b.property
  · intro c hcP
    apply mem_sup_right
    obtain ⟨b,hb⟩ := hf2 ⟨c,hcP⟩
    have hbval : ((f b).2 : G) = c := congrArg (fun z : ↥(P ⊓ C) => (z : G)) hb
    apply (mem_rightAmbient_iff e he hc B c).mpr
    refine ⟨hcP.2,(f b).1,(f b).1.property.2,?_⟩
    rw [←hbval,hc (f b).1.property.2 _ (f b).2.property.2,←hf]
    exact b.property
end Theory.GroupTheory
