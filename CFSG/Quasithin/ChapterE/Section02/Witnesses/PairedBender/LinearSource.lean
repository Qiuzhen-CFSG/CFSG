module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.LinearCoordinates
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Dihedral
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.TwoConjugateProduct.Projection
public import Theory.ElementaryAbelian.Injective

/-!
# The genuine paired linear branch of E.2.7

The original maximal two-core lies in the two actual simple factors, and
multiplication supplies marked Sylow and Borel coordinates. A nontrivial
projection of the original V has order two or at least four. The first case
uses an odd rotation and all of V to give a dihedral quotient; the second
uses the genuine SL₂ two-conjugate theorem and perfect product transport.
Every pair, model, core and Borel conclusion is constructed from the source
hypotheses. Nontriviality of V suffices; its normality in T is not needed here.

Source: Aschbacher–Smith E.2.7, printed p.219, paired Bender paragraph.
The independent component/model selection and n(H) parameter identification
remain with the Chapter E assembly.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender
variable {H : Type*} [Group H] [Finite H]

inductive LinearAlternative (T : Sylow 2 H) (M V : Subgroup H) (n : ℕ) : Prop
  | linear : Nonempty (LinearWitness T M V n) → LinearAlternative T M V n
  | dihedral (p : ℕ) (prime : p.Prime) (odd : p≠2)
      (w : QuotientLift.Pair T M V) (a : ℕ) (positive : 0<a)
      (model : Nonempty (w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore ≃*
        DihedralGroup (p^a))) : LinearAlternative T M V n

private theorem linear_of_nontrivial_first
    {G A F : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [Field F] [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F=2^n)
    (e : G≃*SL(2,F)) (hcoreG : pCore 2 G=⊥) (S : Sylow 2 G) (R : Sylow 2 A)
    (W : Subgroup (G×A)) [IsElementaryAbelian 2 W]
    (hc : W.map (MonoidHom.fst G A) ≠ ⊥)
    (T : Sylow 2 H) (M : Subgroup H) (f : G×A→*H) (hf : Function.Injective f)
    (hT : (T:Subgroup H).comap f=(S:Subgroup G).prod (R:Subgroup A))
    (hM : M.comap f=(normalizer (S:Set G)).prod (normalizer (R:Set A)))
    (hVT : W.map f≤T) (hVM : W.map f≤M.pCoreIn 2) :
    LinearAlternative T M (W.map f) n := by
  let : IsElementaryAbelian 2 (W.map (MonoidHom.fst G A)) := IsElementaryAbelian.map _
  obtain hc | hc := Subgroup.two_or_four_of_elementary_ne_bot _ hc
  · obtain ⟨p,hp,hp2,w,a,ha,he⟩ := exists_dihedral_product W hc hcoreG T M f hf hVT hVM
    exact .dihedral p hp hp2 w a ha he
  · apply LinearAlternative.linear
    have hWS : W ≤ (S : Subgroup G).prod (R : Subgroup A) := by
      rw [← hT]
      exact map_le_iff_le_comap.mp hVT
    have hWM : W.map (MonoidHom.snd G A) ≤ normalizer (R : Set A) :=
      ((le_prod_iff.mp hWS).2).trans (R : Subgroup A).le_normalizer
    exact exists_linear_product hF e S (R : Subgroup A) (normalizer (R : Set A)) W
      hWS hWM hc T M f hf hT hM

theorem source_linear_pair
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1<n) (hF : Nat.card F=2^n)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (hJ : ChapterB.minimalParabolicCore T hP=⊥)
    {K : Subgroup H} (hK : IsComponent H K) (hC : K.IsCComponent)
    [IsSimpleGroup K] (hgen : K⊔(T:Subgroup H)=⊤) (hnot : ¬K.Normal)
    (e : K≃*SL(2,F)) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V≤T) (hVM : V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hV : V≠⊥) : LinearAlternative T (ChapterB.minimalParabolicMax T hP) V n := by
  obtain ⟨c⟩ := source_linear_coordinates hn hF hH T hP hs hJ hK hC hgen hnot e V hVM
  let W := V.comap c.embedding
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    ((c.embedding.comp W.subtype).codRestrict V (fun x=>x.property))
    (by intro x y h; apply Subtype.ext; exact c.injective (congrArg Subtype.val h))
  have hW : W≠⊥ := by
    intro he
    apply hV
    rw [← c.original_image]
    change W.map c.embedding=⊥
    rw [he,Subgroup.map_bot]
  have hrad : solvableRadical H=⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  have hKcore : pCore 2 K=⊥ := SimpleSocle.pCore_eq_bot
    (solvableRadical_eq_bot_of_isSubnormal hrad hK.1) 2
  have hDcore : pCore 2 c.second=⊥ := by
    apply Subgroup.map_injective (f := c.second_model.toMonoidHom) c.second_model.injective
    rw [pCore_map_iso 2 c.second_model]
    have hh := congrArg (Subgroup.map e.toMonoidHom) hKcore
    rw [pCore_map_iso 2 e,Subgroup.map_bot] at hh
    rw [hh,Subgroup.map_bot]
  have hWT : W.map c.embedding≤T := by change (V.comap c.embedding).map c.embedding≤T; rwa [c.original_image]
  have hWM : W.map c.embedding≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2 :=
    by change (V.comap c.embedding).map c.embedding≤_; rwa [c.original_image]
  rcases Subgroup.fst_ne_bot_or_snd_ne_bot W hW with hc | hc
  · have hh := linear_of_nontrivial_first hF e hKcore c.first_sylow c.second_sylow W hc
      T _ c.embedding c.injective c.sylow_preimage c.borel_preimage hWT hWM
    rwa [c.original_image] at hh
  · let z : c.second×K≃*K×c.second := MulEquiv.prodComm
    let W' := W.comap z.toMonoidHom
    let f := c.embedding.comp z.toMonoidHom
    have hzW : W'.map z.toMonoidHom=W := map_comap_eq_self_of_surjective z.surjective W
    let : IsElementaryAbelian 2 W' := IsElementaryAbelian.of_injective
      ((z.toMonoidHom.comp W'.subtype).codRestrict W (fun x=>x.property))
      (by intro x y h; apply Subtype.ext; exact z.injective (congrArg Subtype.val h))
    have hWim : W'.map f=V := by rw [← Subgroup.map_map,hzW]; exact c.original_image
    have hc' : W'.map (MonoidHom.fst c.second K)≠⊥ := by
      have he : W'.map (MonoidHom.fst c.second K)=W.map (MonoidHom.snd K c.second) := by
        rw [← hzW,Subgroup.map_map]
        rfl
      rwa [he]
    have hT' : (T:Subgroup H).comap f=
        (c.second_sylow:Subgroup c.second).prod (c.first_sylow:Subgroup K) := by
      rw [show f=c.embedding.comp z.toMonoidHom from rfl,← comap_comap,c.sylow_preimage]
      ext x
      exact and_comm
    have hM' : (ChapterB.minimalParabolicMax T hP).comap f=
        (normalizer (c.second_sylow:Set c.second)).prod (normalizer (c.first_sylow:Set K)) := by
      rw [show f=c.embedding.comp z.toMonoidHom from rfl,← comap_comap,c.borel_preimage]
      ext x
      exact and_comm
    have hh := linear_of_nontrivial_first hF c.second_model hDcore c.second_sylow c.first_sylow
      W' hc' T _ f (c.injective.comp z.injective) hT' hM' (by rwa [hWim]) (by rwa [hWim])
    rwa [hWim] at hh
end CFSG.Quasithin.ChapterE.Witnesses.PairedBender
