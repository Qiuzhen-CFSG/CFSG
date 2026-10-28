module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeNoncentral
public import Theory.GroupTheory.CentralCoprimeAbelianLift
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel

/-!
# Perfect subgroups through odd ternary central covers

A prime subgroup lifts through a finite central extension to the unique Sylow
subgroup of its nilpotent preimage, retaining the full normalizer preimage.
The perfect residual of a component preimage then descends the solvable-
automizer centralization argument without transferring any SQTK hypothesis.
For cubic kernels, involution centralizers lift surjectively, and their
SL₂ residual maps injectively because its central elements have square one.

Source: Aschbacher--Smith, A.3.21(a),(c), printed pp.55--56.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

theorem prime_lift_central_kernel
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {r : ℕ} [Fact r.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (Q : Subgroup H) (hQ : IsPGroup r Q) :
    ∃ R : Subgroup G, IsPGroup r R ∧ R.map f = Q ∧
      (normalizer (Q : Set H)).comap f ≤ normalizer (R : Set G) := by
  let A := Q.comap f
  let g : A →* Q := f.subgroupComap Q
  have hg : Function.Surjective g := f.subgroupComap_surjective_of_surjective Q hf
  have hgc : g.ker ≤ center A := by
    intro x hx
    have hxk : (x : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc hxk) y)
  let : Group.IsNilpotent Q := hQ.isNilpotent
  let : Group.IsNilpotent A := Subgroup.isNilpotent_of_ker_le_center g hgc
  let P : Sylow r A := Sylow.nonempty.some
  let : (P : Subgroup A).Characteristic := P.characteristic_of_normal inferInstance
  have hPtop : (P.mapSurjective hg : Subgroup Q) = ⊤ := by
    apply top_unique
    exact (hQ.to_subgroup ⊤).le_sylow_of_normal _
  let R : Subgroup G := (P : Subgroup A).map A.subtype
  refine ⟨R,P.isPGroup'.map A.subtype,?_,?_⟩
  · have hh := congrArg (Subgroup.map Q.subtype) hPtop
    change ((P : Subgroup A).map g).map Q.subtype = (⊤ : Subgroup Q).map Q.subtype at hh
    rw [map_map,←MonoidHom.range_eq_map,range_subtype] at hh
    change (P : Subgroup A).map (f.comp A.subtype) = Q at hh
    simpa only [R,map_map] using hh
  · exact (le_of_eq (comap_normalizer_eq_of_surjective Q hf)).trans
      (normalizer_le_normalizer_characteristic_image A (P : Subgroup A))

theorem rankThree_central_quotient_centralizes_odd_core
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p residue : ℕ} (h : RankThreeLocalStructure G p residue)
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    {r : ℕ} [Fact r.Prime] (ho : Odd r) (hne : r ≠ p)
    (B Q : Subgroup H) [Group.IsPerfect B] (hQ : IsPGroup r Q)
    (hBQ : B ≤ normalizer (Q : Set H)) : B ≤ centralizer (Q : Set H) := by
  obtain ⟨R,hR,hRf,hNR⟩ := prime_lift_central_kernel f hf hc Q hQ
  let A := B.comap f
  let K := (solvableResidual A).map A.subtype
  let : Group.IsPerfect K := Group.IsPerfect.map _
  have hKmap : K.map f = B := by
    have hh := map_solvableResidual_comap f hf B
    rw [solvableResidual_eq_top (G := B),←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hKN : K ≤ normalizer (R : Set G) :=
    ((map_subtype_le _).trans (comap_mono hBQ)).trans hNR
  have hKR := rankThree_perfect_centralizes_odd_core h ho hne K R hR hKN
  rw [←hKmap,←hRf]
  exact (map_mono hKR).trans (map_centralizer_le_centralizer_image (R : Set G) f)

private theorem sl2_center_square {q : ℕ} [Fact q.Prime]
    (x : SL(2,ZMod q)) (hx : x ∈ center SL(2,ZMod q)) : x ^ 2 = 1 := by
  obtain ⟨a,ha,h⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  simp only [Fintype.card_fin] at ha
  rcases sq_eq_one_iff.mp ha with rfl | rfl
  · have he : x = 1 := Subtype.ext (by simpa using h.symm)
    simp [he]
  · have he : x = -1 := Subtype.ext (by simpa [←Matrix.diagonal_neg] using h.symm)
    simp [he]

theorem rankThree_cubic_quotient_perfect_embedding
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    {q residue : ℕ} [Fact q.Prime] (h : RankThreeLocalStructure H q residue)
    (f : H →* G) (hf : Function.Surjective f) (hc : f.ker ≤ center H)
    (h3 : ∀ x ∈ f.ker, x ^ 3 = 1)
    (z : G) (hz : orderOf z = 2)
    (B : Subgroup G) [Group.IsPerfect B]
    (hBz : B ≤ centralizer ({z} : Set G)) :
    ∃ i : B →* SL(2,ZMod q), Function.Injective i := by
  obtain ⟨w,hw,rfl⟩ := Matrix.SU3.InnerThreeRank.exists_involution_lift_of_cube_kernel f hf h3 z hz
  let C := centralizer ({w} : Set H)
  let D := centralizer ({f w} : Set G)
  have hCD : C.map f = D :=
    Matrix.SU3.InnerThreeRank.map_centralizer_of_central_cube_kernel f hf hc h3 w
      (by simpa only [hw] using pow_orderOf_eq_one w)
  let π : C →* D := (MulEquiv.subgroupCongr hCD).toMonoidHom.comp (f.subgroupMap C)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hCD).surjective.comp (f.subgroupMap_surjective C)
  obtain ⟨_,_,hh⟩ := h.involutions
  obtain ⟨_,⟨e⟩,hr⟩ := hh w hw
  let R := primeToResidual q C
  let φ := π.comp R.subtype
  have hφ : Function.Injective φ := by
    apply (injective_iff_map_eq_one φ).mpr
    intro x hx
    have hxk : (x.val.val : H) ∈ f.ker := congrArg Subtype.val hx
    have hec : e x ∈ center SL(2,ZMod q) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      rw [←map_mul,←map_mul]
      congr 1
      exact Subtype.ext (Subtype.ext (mem_center_iff.mp (hc hxk) y.val.val))
    have hs := sl2_center_square (e x) hec
    have ht : e x ^ 3 = 1 := by
      rw [←map_pow]
      exact (congrArg e (show x ^ 3 = 1 from Subtype.ext (Subtype.ext (h3 _ hxk)))).trans (map_one e)
    rw [pow_succ,hs,one_mul] at ht
    exact e.injective (ht.trans (map_one e).symm)
  let j := inclusion hBz
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hle : j.range ≤ φ.range := by
    have h1 := le_solvableResidual_of_isPerfect j.range
    have h2 : solvableResidual D ≤ R.map π := by
      rw [←map_solvableResidual_eq π hπ]
      exact map_mono hr
    simpa only [φ, MonoidHom.range_comp,range_subtype] using h1.trans h2
  let a := MonoidHom.ofInjective hφ
  let i := e.toMonoidHom.comp (a.symm.toMonoidHom.comp (j.codRestrict _ (fun b => hle ⟨b,rfl⟩)))
  refine ⟨i,e.injective.comp (a.symm.injective.comp ?_)⟩
  intro x y hh
  exact Subtype.ext (congrArg (fun v => v.val.val) hh)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
