module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableSeedSplitting

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneSymmetricQuotient
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.RankOneNormalClosure

/-!
# The literal S3 quotient and split VH-plane in the solvable seed branch

The previously constructed quotient map from K/C_K(VH) to dotted K is
transported to the exact action image in H/C_H(VH). Its kernel is the
image of K intersect C_H(U-hat), hence normal in the whole H-action.
The surviving rank-one involution and this literal map exclude the
quasisimple, two-factor and hyperplane B.5 cases. The rank-one offender
argument excludes the outer A6--C3 case. Thus the actual VH-action is S3.

Applying the checked splitting consumer now proves C_K(VH)=C_K(U-hat)
and VH=[VH,K] plus C_VH(K), with the original commutator plane of dimension
two. No S3 model for the VH-action is an extra premise.

The earlier marked SolvableSeedRow still requires construction at its
14.3.23--24 source boundary. Extending the splitting to all Z(U), completing
14.3.25 and the remaining centerlessness contradictions stay with the
centerlessness owner; this module does not prove those statements.

Source: Aschbacher--Smith 14.3.25, printed p.1001, using B.5.6 and G.6.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal symmetric-three quotient of the VH-action has kernel normal
in the full H-action, and agrees with the original dotted quotient on K. -/
theorem source_solvable_seed_action_quotient (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal) :
    letI := hn
    let K := solvableSeedActor F g
    let q := QuotientGroup.mk' (centralizer
      ((faithfulTestModule F L).subgroupOf F.H : Set F.H))
    let r := QuotientGroup.mk' F.uhatAction.ker
    let D := K.map q
    ∃ (e : K.map r ≃* Equiv.Perm (Fin 3)) (f : D →* Equiv.Perm (Fin 3)),
      Function.Surjective f ∧
      (∀ k : K, f ⟨q k,mem_map_of_mem q k.property⟩ =
        e ⟨r k,mem_map_of_mem r k.property⟩) ∧
      (f.ker.map D.subtype).Normal := by
  let := hn
  dsimp only
  let K := solvableSeedActor F g
  let C := centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)
  let q := QuotientGroup.mk' C
  let r := QuotientGroup.mk' F.uhatAction.ker
  let D := K.map q
  obtain ⟨hnC,f₀,hf₀,heval,em⟩ := source_solvable_seed_quotient d earlier hq chosen
    structural alternatives F hne hz g hgP row
  let := hnC
  obtain ⟨e₀,he₀⟩ := solvable_seed_action_equiv (L := L) F g hn
  obtain ⟨e⟩ := em
  let f : D →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (f₀.comp e₀.symm.toMonoidHom)
  have hf : Function.Surjective f := e.surjective.comp (hf₀.comp e₀.symm.surjective)
  have he (k : K) : f ⟨q k,mem_map_of_mem q k.property⟩ =
      e ⟨r k,mem_map_of_mem r k.property⟩ := by
    have heD : (⟨q k,mem_map_of_mem q k.property⟩ : D) =
        e₀ (QuotientGroup.mk' (C.comap K.subtype) k) := Subtype.ext (he₀ k).symm
    change e (f₀ (e₀.symm _)) = _
    rw [heD,e₀.symm_apply_apply]
    apply congrArg e
    exact Subtype.ext (heval k)
  refine ⟨e,f,hf,he,?_⟩
  have hk : f.ker.map D.subtype = (K ⊓ F.uhatAction.ker).map q := by
    apply le_antisymm
    · rintro x ⟨b,hb,rfl⟩
      obtain ⟨k,hk,hqb⟩ := b.property
      let kK : K := ⟨k,hk⟩
      have hbe : b = ⟨q k,mem_map_of_mem q hk⟩ := Subtype.ext hqb.symm
      have hh : e ⟨r k,mem_map_of_mem r hk⟩ = 1 := by
        rw [←he kK,←hbe]
        exact hb
      have hkhat : k ∈ F.uhatAction.ker := by
        apply (QuotientGroup.eq_one_iff k).mp
        exact congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
      exact ⟨k,⟨hk,hkhat⟩,hqb⟩
    · rintro x ⟨k,⟨hk,hkhat⟩,rfl⟩
      refine ⟨⟨q k,mem_map_of_mem q hk⟩,?_,rfl⟩
      change f ⟨q k,mem_map_of_mem q hk⟩ = 1
      rw [he ⟨k,hk⟩]
      have hh : (⟨r k,mem_map_of_mem r hk⟩ : K.map r) = 1 :=
        Subtype.ext ((QuotientGroup.eq_one_iff k).mpr hkhat)
      rw [hh,map_one]
  rw [hk]
  exact Normal.map inferInstance q (QuotientGroup.mk'_surjective C)

/-- All nonsymmetric rows of the actual VH-action classification are excluded.
The original quotient kernel's ambient normality is constructed, not assumed. -/
theorem source_solvable_seed_symmetricThree (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    let W := (faithfulTestModule F L).subgroupOf F.H
    ∃ hn : W.Normal, ∃ he : IsElementaryAbelian 2 W, letI := hn; letI := he
    let C := centralizer (W : Set F.H)
    let q := QuotientGroup.mk' C
    let σ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let D := (solvableSeedActor F g).map q
    Nonempty (SymmetricThreeCase (σ.comp D.subtype)) := by
  dsimp only
  obtain ⟨hn,he,hcore,a,ha,hhat,hr,hsq⟩ := source_solvable_seed_rank_one d earlier hq chosen
    structural alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  refine ⟨hn,he,?_⟩
  let W := (faithfulTestModule F L).subgroupOf F.H
  let C := centralizer (W : Set F.H)
  let q := QuotientGroup.mk' C
  let σ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let D := (solvableSeedActor F g).map q
  obtain ⟨_,_,hf,hc⟩ := source_solvable_seed_classification d earlier hq chosen structural
    alternatives F hne hz g hgP hgH row
  obtain ⟨e,f,hf',heval,hkernel⟩ := source_solvable_seed_action_quotient d earlier hq chosen
    structural alternatives F hne hz g hgP row hn
  have hD := source_solvable_seed_normal_closure d earlier hq chosen structural alternatives
    F hne g hgP hgH row a ha hhat hn
  have haK : a ∈ solvableSeedActor F g := le_conjugateSpanBy _ _ ha
  have haD : q a ∈ D := mem_map_of_mem q haK
  have hσ (b : F.H) : σ (q b) = NormalElementaryQuotient.originalAction W b := by
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) b w).trans
        (NormalElementaryQuotient.originalAction_apply W b w).symm
  have ht2 : q a ^ 2 = 1 := by
    apply NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    rw [←map_pow,map_one,hσ]
    exact hsq
  have htf : f ⟨q a,haD⟩ ≠ 1 := by
    rw [heval ⟨a,haK⟩]
    intro hh
    have hh' := congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
    exact hhat ((QuotientGroup.eq_one_iff a).mp hh')
  have hr' : Module.finrank (ZMod 2)
      ((σ.comp D.subtype) ⟨q a,haD⟩ - LinearMap.id).range ≤ 1 := by
    change Module.finrank (ZMod 2) (σ (q a) - LinearMap.id).range ≤ 1
    rw [hσ]
    exact hr.le
  cases hc with
  | quasisimple hquasi c =>
      let := hquasi
      exact (c.no_symmetricThree_quotient f hf').elim
  | symmetricThree c => exact ⟨c⟩
  | twoFactors c =>
      exact (c.no_normalClosure_symmetricThree_quotient D (q a) haD hD
        (σ.comp D.subtype) hf.twoCore f hf' hkernel ht2 htf hr').elim
  | outerSixThree c =>
      have hqa : q a ≠ 1 := by
        intro hh
        have hh' : (⟨q a,haD⟩ : D) = 1 := Subtype.ext hh
        exact htf ((congrArg f hh').trans f.map_one)
      have hr'' : Module.finrank (ZMod 2)
          ((σ.comp D.subtype) ⟨q a,haD⟩ - LinearMap.id).range = 1 := by
        change Module.finrank (ZMod 2) (σ (q a) - LinearMap.id).range = 1
        rw [hσ]
        exact hr
      exact (ChapterG.Section06.no_outerShape_of_rank_one_normalClosure
        D (q a) haD hD (σ.comp D.subtype) hf ht2 hqa hr'' c).elim
  | hyperplane c =>
      exact (c.no_normalClosure_symmetricThree_quotient D (q a) haD hD
        (σ.comp D.subtype) hf.faithful hf.twoCore f hf' hkernel htf hr').elim

/-- The original relative centralizer quotient is S3, with no additional
model assumption on the action of K on VH. -/
theorem source_solvable_seed_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal) :
    letI := hn
    let K := solvableSeedActor F g
    let C := (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap K.subtype
    Nonempty ((K ⧸ C) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((K.map (QuotientGroup.mk' (centralizer
        ((faithfulTestModule F L).subgroupOf F.H : Set F.H)))) ≃* Equiv.Perm (Fin 3)) := by
  let := hn
  obtain ⟨_,_,⟨c⟩⟩ := source_solvable_seed_symmetricThree d earlier hq chosen structural
    alternatives F hne hz g hgP hgH row
  obtain ⟨e,_⟩ := solvable_seed_action_equiv (L := L) F g hn
  exact ⟨⟨e.trans c.equiv⟩,⟨c.equiv⟩⟩

/-- The original surjection to dotted K is an isomorphism, with its evaluation
on every element of K retained. This identifies the source's literal quotients. -/
theorem source_solvable_seed_quotient_equiv (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g)
    (hn : ((faithfulTestModule F L).subgroupOf F.H).Normal) :
    letI := hn
    let K := solvableSeedActor F g
    let C := (centralizer ((faithfulTestModule F L).subgroupOf F.H : Set F.H)).comap K.subtype
    let r := QuotientGroup.mk' F.uhatAction.ker
    ∃ e : (K ⧸ C) ≃* K.map r,
      ∀ k : K, (e (QuotientGroup.mk' C k) : Hdot F F.uhatAction) = r k := by
  let := hn
  dsimp only
  obtain ⟨hnC,f,hf,heval,hem⟩ := source_solvable_seed_quotient d earlier hq chosen
    structural alternatives F hne hz g hgP row
  let := hnC
  obtain ⟨⟨em⟩,_⟩ := source_solvable_seed_model d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn
  obtain ⟨ed⟩ := hem
  have hi : Function.Injective f := (hf.bijective_of_nat_card_le
    ((Nat.card_congr em.toEquiv).trans (Nat.card_congr ed.toEquiv).symm).le).1
  exact ⟨MulEquiv.ofBijective f ⟨hi,hf⟩,heval⟩

/-- Source 14.3.25's kernel equality and split VH-plane now follow from the
original marked row, without an assumed S3 identification of the VH-action. -/
theorem source_solvable_seed_kernel_and_plane (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hz : centralLTSeed F L ≠ ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) (row : SolvableSeedRow F L g) :
    let W := (faithfulTestModule F L).subgroupOf F.H
    ∃ hn : W.Normal, ∃ he : IsElementaryAbelian 2 W, letI := hn; letI := he
    let K := solvableSeedActor F g
    (centralizer (W : Set F.H)).comap K.subtype =
        (F.uhatAction.comp K.subtype).ker ∧
      IsCompl (NormalElementaryQuotient.commutatorSpace W K)
        (fixedSpace (NormalElementaryQuotient.originalAction W) K) ∧
      Module.finrank (ZMod 2) (NormalElementaryQuotient.commutatorSpace W K) = 2 := by
  obtain ⟨hn,he,_⟩ := source_solvable_seed_symmetricThree d earlier hq chosen structural
    alternatives F hne hz g hgP hgH row
  let := hn
  let := he
  have hm := (source_solvable_seed_model d earlier hq chosen structural alternatives
    F hne hz g hgP hgH row hn).2
  exact ⟨hn,he,source_solvable_seed_kernel_eq_of_model d earlier hq chosen structural
    alternatives F hne hz g hgP row hn hm,
    source_solvable_seed_plane_of_model d earlier hq chosen structural alternatives
      F hne hz g hgP hgH row hn he hm⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
