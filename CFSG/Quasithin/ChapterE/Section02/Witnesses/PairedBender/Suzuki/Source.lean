module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Suzuki.Coordinates
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Suzuki.Product
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Dihedral
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.TwoConjugateProduct.Projection
public import Theory.ElementaryAbelian.Injective

/-!
# The genuine paired Suzuki branch of E.2.7

The original maximal two-core lies in the two actual simple factors, and
multiplication supplies marked Sylow and Borel coordinates. A nontrivial
projection of the original V has order two or at least four. The first case
uses an odd rotation and all of V to give a dihedral quotient; the second
uses the genuine Suzuki two-conjugate theorem and perfect product transport.
Every pair, model, core and Borel conclusion is constructed from the source
hypotheses. Nontriviality of V suffices; its normality in T is not needed here.

Source: Aschbacher–Smith E.2.7, printed p.219, paired Bender paragraph.
The independent component/model selection and n(H) parameter identification
remain with the Chapter E assembly.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender.Suzuki
variable {H : Type*} [Group H] [Finite H]

private theorem of_nontrivial_first
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {m : ℕ} (hm : 0<m) (e : G≃*SuzukiMatrixGroup m) (hcoreG : pCore 2 G=⊥) (S : Sylow 2 G) (R : Sylow 2 A)
    (W : Subgroup (G×A)) [IsElementaryAbelian 2 W]
    (hc : W.map (MonoidHom.fst G A) ≠ ⊥)
    (T : Sylow 2 H) (M : Subgroup H) (f : G×A→*H) (hf : Function.Injective f)
    (hT : (T:Subgroup H).comap f=(S:Subgroup G).prod (R:Subgroup A))
    (hM : M.comap f=(normalizer (S:Set G)).prod (normalizer (R:Set A)))
    (hVT : W.map f≤T) (hVM : W.map f≤M.pCoreIn 2) :
    Nonempty (BenderPlacement.OriginalWitness T M (W.map f) (2*m+1)) := by
  let : IsElementaryAbelian 2 (W.map (MonoidHom.fst G A)) := IsElementaryAbelian.map _
  obtain hc | hc := Subgroup.two_or_four_of_elementary_ne_bot _ hc
  · obtain ⟨p,hp,hp2,w,a,ha,he⟩ := exists_dihedral_product W hc hcoreG T M f hf hVT hVM
    obtain ⟨d⟩ := he
    exact ⟨⟨w,1,by decide,one_dvd _,.dihedral rfl p a hp hp2 ha d⟩⟩
  · have hWS : W ≤ (S : Subgroup G).prod (R : Subgroup A) := by
      rw [← hT]
      exact map_le_iff_le_comap.mp hVT
    have hWM : W.map (MonoidHom.snd G A) ≤ normalizer (R : Set A) :=
      ((le_prod_iff.mp hWS).2).trans (R : Subgroup A).le_normalizer
    exact exists_product hm e S (R : Subgroup A) (normalizer (R : Set A)) W
      hWS hWM hc T M f hf hT hM

/-- The full paired Suzuki source construction on the original elementary subgroup.
The original maximal subgroup, Sylow intersection, normal core and model degree
are retained. The actual Suzuki model also supplies simplicity and nonsolvability. -/
theorem source
    {m : ℕ} (hm : 0<m)
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP=⊥)
    {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K⊔(T:Subgroup H)=⊤) (hnot : ¬K.Normal)
    (e : K≃*SuzukiMatrixGroup m) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V≤T) (hVM : V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hV : V≠⊥) : Nonempty (BenderPlacement.OriginalWitness T (ChapterB.minimalParabolicMax T hP) V (2*m+1)) := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup K := e.isSimpleGroup
  have hs : ¬ Group.IsSolvable H := by
    intro hsol
    let := hsol
    exact BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
      (Group.isSolvable_of_isSolvable_injective (f:=K.subtype.comp e.symm.toMonoidHom)
        (K.subtype_injective.comp e.symm.injective))
  obtain ⟨c⟩ := source_coordinates hm hH T hP hs hJ hK hgen hnot e V hVM
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
  · have hh := of_nontrivial_first hm e hKcore c.first_sylow c.second_sylow W hc
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
    have hh := of_nontrivial_first hm c.second_model hDcore c.second_sylow c.first_sylow
      W' hc' T _ f (c.injective.comp z.injective) hT' hM' (by rwa [hWim]) (by rwa [hWim])
    rwa [hWim] at hh
end CFSG.Quasithin.ChapterE.Witnesses.PairedBender.Suzuki
