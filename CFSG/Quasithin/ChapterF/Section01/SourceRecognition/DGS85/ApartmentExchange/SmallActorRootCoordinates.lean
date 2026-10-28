module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorQuotient
public import Theory.SpecificGroups.SL2.OppositeSylowMarking

/-!
# Coordinates on the two actual six-path radicals

Odd seven-path fixers make both radicals inject into the original midpoint
quotient. Their regular exit actions give full Sylow orders and distinguish
the two images. One inner change of the same quotient marking consequently
sends them to the full upper and lower transvection groups. The own-core
kernel and original root inclusions are retained.

Source: DGS, Groups and Graphs (1985), (14.1)--(14.3), pp.210--212.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
  (d : SixPathSmallActorGeometry c)

/-- The original midpoint quotient simultaneously marks both complete
six-path radicals as opposite unipotent subgroups. -/
theorem source_six_root_coordinates
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hlen : p.length=12)
    (hT : ∀ z∈p.support, z∈cartanApartment A (reflectionGroup c d.reflection))
    (e : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
      pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,k)) :
    Nat.card ((sourceGraph A).neighborSet (p.getVert 6)) = Nat.card k+1 →
    let D := halfPathActor (X := (A).Universal) p 6
    let R := (pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf D
    let U := (pathRoot (X := (A).Universal) (p.take 6)).subgroupOf D
    let f := halfPathLinearMap h p 6 hlen e
    R ⊓ f.ker=⊥ ∧ U ⊓ f.ker=⊥ ∧
      ∃ z : SL(2,k),
        R.map ((MulAut.conj z).toMonoidHom.comp f)=Matrix.SpecialLinearGroup.upperUnipotent k ∧
        ∀ y : SL(2,k), y∈U.map ((MulAut.conj z).toMonoidHom.comp f) ↔
          ∃ a : k, Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y := by
  intro hval D R U f
  let l := p.take 6
  let r := (p.drop 6).reverse
  have hl : l.length=6 := by simp only [l,take_length,hlen]; decide
  have hr : r.length=6 := by simp only [r,length_reverse,drop_length,hlen]
  have hlnil : ¬l.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hrnil : ¬r.Nil := by intro hh; have := hh.length_eq_zero; omega
  have hprevl : l.penultimate=p.getVert 5 := by
    simp only [penultimate,hl,l,take_getVert]; rfl
  have hprevr : r.penultimate=p.getVert 7 := by
    simp only [penultimate,hr,r,getVert_reverse,drop_length,hlen,drop_getVert]
  have hdiff : l.penultimate≠r.penultimate := by
    rw [hprevl,hprevr]
    intro he
    have := hp.getVert_injOn (by omega : 5≤p.length) (by omega : 7≤p.length) he
    omega
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hTl : ∀ z∈l.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    intro z hz
    rw [support_take] at hz
    exact hT z (List.mem_of_mem_take hz)
  have hTr : ∀ z∈r.support, z∈cartanApartment A (reflectionGroup c d.reflection) := by
    intro z hz
    simp only [r,support_reverse,List.mem_reverse] at hz
    rw [drop_support_eq_support_drop_min] at hz
    exact hT z (List.mem_of_mem_drop hz)
  have hK (z) (hz : z∈cartanApartment A (reflectionGroup c d.reflection)) :
      ∀ k∈cartan c, k • z=z :=
    fun k hk => reflectionApartment_fixed c d.reflection d.normalizes k hk z hz
  have hfac (u v) (q : (sourceGraph A).Walk u v) (hqpos : 0<q.length)
      (hqT : ∀ z∈q.support, z∈cartanApartment A (reflectionGroup c d.reflection)) :=
    apartment_path_factorization h c 6 (by decide) d.reflection d.fixes d.moves d.squares
      d.normalizes d.transitive d.thick q hqpos hqT
  have : Finite ((sourceGraph A).neighborSet (p.getVert 6)) :=
    Nat.finite_of_card_ne_zero (by rw [hval]; omega)
  have hnewr : r.penultimate∉l.support := by
    intro hm
    exact hdiff.symm (htree.eq_penultimate_of_adj_end (hp.take 6) (r.adj_penultimate hrnil).symm hm)
  have hnewl : l.penultimate∉r.support := by
    intro hm
    exact hdiff (htree.eq_penultimate_of_adj_end (hp.drop 6).reverse (l.adj_penultimate hlnil).symm hm)
  have hoddp := d.odd (l.concat (r.adj_penultimate hrnil).symm)
    ((hp.take 6).concat hnewr _) (by rw [length_concat,hl])
  have hoddq := d.odd (r.concat (l.adj_penultimate hlnil).symm)
    ((hp.drop 6).reverse.concat hnewl _) (by rw [length_concat,hr])
  let R' := (pathRoot (X := (A).Universal) r).subgroupOf D
  have hR : R'=R := by dsimp only [R',R,r]; rw [pathRoot_reverse]
  have hRle : pathRoot (X := (A).Universal) r ≤ D := by
    dsimp only [r]
    rw [pathRoot_reverse]
    exact le_sup_left
  have hcR : Nat.card R'=Nat.card k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRle).toEquiv]
    have hh := card_pathRoot_add_one htree (source_action A) r (hp.drop 6).reverse hrnil
      (by rw [hr]; exact d.transitive) (cartan c)
      ⟨l.penultimate,(l.adj_penultimate hlnil).symm,hdiff⟩
      (hK _ (hTl _ (l.getVert_mem_support _))) (hfac _ _ r (by omega) hTr) hoddq
    exact Nat.add_right_cancel (hh.trans hval)
  have hcU : Nat.card U=Nat.card k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show pathRoot (X := (A).Universal) l ≤ D from le_sup_right)).toEquiv]
    have hh := card_pathRoot_add_one htree (source_action A) l (hp.take 6) hlnil
      (by rw [hl]; exact d.transitive) (cartan c)
      ⟨r.penultimate,(r.adj_penultimate hrnil).symm,hdiff.symm⟩
      (hK _ (hTr _ (r.getVert_mem_support _))) (hfac _ _ l (by omega) hTl) hoddp
    exact Nat.add_right_cancel (hh.trans hval)
  have hrk : R' ⊓ f.ker=⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hh : (x:(A).Universal)∈pathRoot (X := (A).Universal) r ⊓
        MulAction.stabilizer (A).Universal l.penultimate :=
      ⟨hx.1,halfPathLinearMap_kernel_fixes_neighbors h p 6 hlen e x hx.2 _
        (l.adj_penultimate hlnil).symm⟩
    rwa [pathRoot_inf_stabilizer_eq_bot r _ hoddq] at hh
  have huk : U ⊓ f.ker=⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hh : (x:(A).Universal)∈pathRoot (X := (A).Universal) l ⊓
        MulAction.stabilizer (A).Universal r.penultimate :=
      ⟨hx.1,halfPathLinearMap_kernel_fixes_neighbors h p 6 hlen e x hx.2 _
        (r.adj_penultimate hrnil).symm⟩
    rwa [pathRoot_inf_stabilizer_eq_bot l _ hoddp] at hh
  have hne : R'.map f≠U.map f := by
    intro he
    have hc : 1<Nat.card R' := by
      rw [hcR]
      let _ : Fintype k := Fintype.ofFinite k
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hrne : R'≠⊥ := by intro hh; rw [hh,card_bot] at hc; omega
    obtain ⟨x,hx,hxne⟩ := R'.bot_or_exists_ne_one.resolve_left hrne
    obtain ⟨y,hy,hxy⟩ := he ▸ mem_map_of_mem f hx
    have hxk : y⁻¹*x∈f.ker := f.eq_iff.mp hxy.symm
    have hyfix : (y:(A).Universal) • l.penultimate=l.penultimate := (pathRoot_fixes l hy).2
    have hxfix : (x:(A).Universal) • l.penultimate=l.penultimate := by
      have hh := halfPathLinearMap_kernel_fixes_neighbors h p 6 hlen e (y⁻¹*x) hxk _
        (l.adj_penultimate hlnil).symm
      have hh' := congrArg (fun z => (y:(A).Universal) • z) hh
      simpa only [coe_mul,coe_inv,mul_smul,smul_inv_smul,hyfix] using hh'
    have hh : (x:(A).Universal)∈pathRoot (X := (A).Universal) r ⊓
        MulAction.stabilizer (A).Universal l.penultimate := ⟨hx,hxfix⟩
    rw [pathRoot_inf_stabilizer_eq_bot r _ hoddq] at hh
    exact hxne (Subtype.ext hh)
  obtain ⟨P,hP⟩ := Matrix.SpecialLinearGroup.two_subgroup_image_is_sylow f R'
    (pathRoot_isTwo r).comap_subtype hcR hrk
  obtain ⟨Q,hQ⟩ := Matrix.SpecialLinearGroup.two_subgroup_image_is_sylow f U
    (pathRoot_isTwo l).comap_subtype hcU huk
  have hPQ : P≠Q := by
    intro hh
    exact hne (hP.symm.trans ((congrArg Sylow.toSubgroup hh).trans hQ))
  obtain ⟨z,hzP,hzQ⟩ := Matrix.SpecialLinearGroup.exists_opposite_sylow_marking 2 P Q hPQ
  rw [hP,hR,Subgroup.map_map] at hzP
  rw [hQ,Subgroup.map_map] at hzQ
  exact ⟨hR ▸ hrk,huk,z,hzP,hzQ⟩


end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
