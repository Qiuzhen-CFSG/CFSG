module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.OctagonRecognition
public import Theory.SpecificGroups.ReeF4.SourceCompletion.AmalgamActions
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import Theory.GroupTheory.Amalgam.AutomorphismGroup
public import Theory.GroupAction.RankTwoCosetCover.SmallCover
public import Theory.GroupAction.DihedralPolygon
public import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Extending compatible actions of the native general Ree amalgam

Every automorphism of the full native linear/Borel/Suzuki amalgam extends
uniquely to the complete Ree group at every positive parameter, including q=8.
The native Cartan calculation supplies the mixed eighth-power relation for
its transformed reflections. Pairing the native completion with its twist
therefore gives a sixteen-cycle. Nine-path transitivity gives diameter eight,
and the two small-cover projections are bijective. Their quotient retains
both endpoint markings. Generation gives uniqueness and the homomorphism law;
the full Borel restriction and faithfulness are retained explicitly.

The covering transport is proved over abstract carriers so checking it does
not repeatedly unfold the concrete native matrix group. The local relation
and all geometry premises are discharged in the native specialization.

This constructs the compatible native action needed by source 5.3.2. The
simultaneous full-normalizer extension diagram, ambient order comparison and
recognition of an arbitrary source completion remain separate obligations.
Source: Aschbacher–Smith 5.3.2, F.3.6 and F.4.3,10,16–17,
printed pp.659,272,274,279,282–283 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open ReeF4.SourceCompletion
universe u
variable {m : ℕ} (hm : 0<m)

private theorem pair_overlap {X Y Z : Type u} {M N : Type*}
    [Group X] [Group Y] [Group Z] [Group M] [Group N]
    {α : RankTwoAmalgam X Y Z}
    (c : α.FaithfulCompletion (G := M)) (d : α.FaithfulCompletion (G := N))
    (hc : c.left.range ⊓ c.right.range = c.middle.range) :
    (c.pairCompletion d).left.range ⊓ (c.pairCompletion d).right.range =
      (c.pairCompletion d).middle.range := by
  let e := c.pairCompletion d
  apply le_antisymm _ (le_inf e.middle_le_left e.middle_le_right)
  rintro z ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hxy : c.left x=c.right y := by
    have he := congrArg (c.pairFst d) (hx.trans hy.symm)
    simpa only [e,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using he
  obtain ⟨b,hb⟩ := hc.le ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩
  have hbx : α.left b=x := c.left_injective hb
  exact ⟨b,by change e.left _=z; rw [hbx]; exact hx⟩

private theorem pair_equiv {X Y Z : Type u} {M N : Type*}
    [Group X] [Group Y] [Group Z] [Group M] [Group N]
    {α : RankTwoAmalgam X Y Z}
    (c : α.FaithfulCompletion (G := M)) (d : α.FaithfulCompletion (G := N))
    (hf : Function.Bijective (c.pairFst d)) (hk : Function.Bijective (c.pairSnd d)) :
    ∃ f : M ≃* N,
      (∀ x, f (c.left x)=d.left x) ∧ (∀ x, f (c.right x)=d.right x) := by
  let e := c.pairCompletion d
  let f := MulEquiv.ofBijective (c.pairFst d) hf
  let k := MulEquiv.ofBijective (c.pairSnd d) hk
  refine ⟨f.symm.trans k,?_,?_⟩
  · intro x
    have h : f (e.left x) = c.left x := c.pairFst_left d x
    have hi : f.symm (c.left x)=e.left x := (congrArg f.symm h).symm.trans (f.symm_apply_apply _)
    change k (f.symm (c.left x))=d.left x
    rw [hi]
    exact c.pairSnd_left d x
  · intro x
    have h : f (e.right x) = c.right x := c.pairFst_right d x
    have hi : f.symm (c.right x)=e.right x := (congrArg f.symm h).symm.trans (f.symm_apply_apply _)
    change k (f.symm (c.right x))=d.right x
    rw [hi]
    exact c.pairSnd_right d x
private theorem exists_marked_pair_equiv {X Y Z : Type u} {M N : Type*}
    [Group X] [Group Y] [Group Z] [Group M] [Group N]
    {α : RankTwoAmalgam X Y Z}
    (c : α.FaithfulCompletion (G := M)) (d : α.FaithfulCompletion (G := N))
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hd : d.left.range ⊓ d.right.range = d.middle.range)
    (s₀ : X) (t₀ : Z) (hs₀ : s₀^2=1) (ht₀ : t₀^2=1)
    (hsout₀ : c.left s₀∉c.middle.range) (htout₀ : c.right t₀∉c.middle.range)
    (hcR : (c.left s₀*c.right t₀)^8=1) (hdR : (d.left s₀*d.right t₀)^8=1)
    (hg : ∀ v (p : (graph (c.pairCompletion d).cosetFamily).Walk v v),
      p.IsCycle → 16≤p.length)
    (hnine : ∀ v, RootPathTransitive (graph (c.pairCompletion d).cosetFamily) (c.Pair d) v 9)
    (hcg : ∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 16≤p.length)
    (hdg : ∀ v (p : (graph d.cosetFamily).Walk v v), p.IsCycle → 16≤p.length) :
    ∃ f : M ≃* N,
      (∀ x, f (c.left x)=d.left x) ∧ (∀ x, f (c.right x)=d.right x) := by
  let e := c.pairCompletion d
  have heO := pair_overlap c d hc
  let s := e.left s₀
  let t := e.right t₀
  have hs : s^2=1 := by
    change (e.left _)^2=1
    rw [←map_pow,hs₀,map_one]
  have ht : t^2=1 := by
    change (e.right _)^2=1
    rw [←map_pow,ht₀,map_one]
  have hst : (s*t)^8=1 := by
    apply Subtype.ext
    apply Prod.ext
    · have h : c.pairFst d ((s*t)^8)=1 := by
        simpa only [s,t,e,map_pow,map_mul,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
          RankTwoAmalgam.FaithfulCompletion.pairFst_right] using
            hcR
      exact h
    · have h : c.pairSnd d ((s*t)^8)=1 := by
        simpa only [s,t,e,map_pow,map_mul,RankTwoAmalgam.FaithfulCompletion.pairSnd_left,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_right] using
            hdR
      exact h
  have hsout : s∉e.middle.range := by
    rintro ⟨b,hb⟩
    apply hsout₀
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [RankTwoAmalgam.FaithfulCompletion.middle, MonoidHom.comp_apply,
      s,e,RankTwoAmalgam.FaithfulCompletion.pairFst_left] using hh
  have htout : t∉e.middle.range := by
    rintro ⟨b,hb⟩
    apply htout₀
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [RankTwoAmalgam.FaithfulCompletion.middle, MonoidHom.comp_apply,
      t,e,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hh
  have hconn : (graph e.cosetFamily).Connected := RankTwo.connected _ e.generated
  let ga : GraphAction (graph e.cosetFamily) (c.Pair d) := {
    map_adj g := (translationGraphIso e.cosetFamily g).toHom.map_adj }
  have hu : (graph e.cosetFamily).UniqueGeodesicsBelow 8 := by
    intro x y p q hp hq hd
    by_contra hh
    obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
      (q.isPath_of_length_eq_dist hq) hh
    have := hg v r hr
    omega
  let action : GroupAction.DihedralPolygon.BipartiteAction (c.Pair d) (graph e.cosetFamily) := {
    color := (·.type)
    adjacent_color h := h.1
    smul_adj := ga.map_adj
    smul_color _ _ := rfl }
  have hfix (g : c.Pair d) (i : Bool) :
      g • RankTwo.base e.cosetFamily i=RankTwo.base e.cosetFamily i ↔
        g∈e.cosetFamily i := by
    change g∈RankTwo.stabilizer e.cosetFamily (RankTwo.base e.cosetFamily i) ↔ _
    simp only [RankTwo.stabilizer,RankTwo.base,stabilizer_base]
  have hsl : s • RankTwo.base e.cosetFamily true≠RankTwo.base e.cosetFamily true := by
    intro h
    exact hsout (heO.le ⟨⟨_,rfl⟩,(hfix s true).mp h⟩)
  have htx : t • RankTwo.base e.cosetFamily false≠RankTwo.base e.cosetFamily false := by
    intro h
    exact htout (heO.le ⟨(hfix t false).mp h,⟨_,rfl⟩⟩)
  let emb : cycleGraph 16 ↪g (graph e.cosetFamily) := GroupAction.DihedralPolygon.edgeEmbedding action
    (by decide : 1<8) hu (by decide : 0<8) le_rfl
    ⟨Bool.false_ne_true,incident_base e.cosetFamily false true⟩ hs ht
    ((hfix s false).mpr ⟨_,rfl⟩) hsl ((hfix t true).mpr ⟨_,rfl⟩) htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  have hcycle := (cycleGraph_isContained_iff (by decide : 2<16)).mp ⟨emb.toCopy⟩
  have hdiam : ∀v w,(graph e.cosetFamily).dist v w≤8 := by
    apply OctagonRecognition.diameter_bound_of_nine_endpoint_bound hconn
    intro v p hp
    exact OctagonRecognition.nine_endpoint_bound ga hnine
      (·.type) (fun h => h.1) (fun h => (same_orbit_iff e.cosetFamily _ _).mpr h) hcycle p hp
  have hf : CoverData e.cosetFamily c.cosetFamily (c.pairFst d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairFst_left d x) (by ext x; exact c.pairFst_right d x) heO hc
  have hk : CoverData e.cosetFamily d.cosetFamily (c.pairSnd d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairSnd_left d x) (by ext x; exact c.pairSnd_right d x) heO hd
  have hif := hf.injective_of_diameter_lt_girth hconn hdiam
    (fun v p hp => (show (8:ℕ)<16 by decide).trans_le (hcg v p hp))
  have hik := hk.injective_of_diameter_lt_girth hconn hdiam
    (fun v p hp => (show (8:ℕ)<16 by decide).trans_le (hdg v p hp))
  exact pair_equiv c d ⟨hif,hf.surjective⟩ ⟨hik,hk.surjective⟩

private theorem ofSubgroups_left_out {F : Type*} [Group F]
    (P B Q : Subgroup F) (hP : B≤P) (hQ : B≤Q) (hgen : P⊔Q=⊤)
    (x : P) (hx : x.val∉B) :
    (RankTwoAmalgam.FaithfulCompletion.ofSubgroups P B Q hP hQ hgen).left x ∉
      (RankTwoAmalgam.FaithfulCompletion.ofSubgroups P B Q hP hQ hgen).middle.range := by
  rintro ⟨b,hb⟩
  change b.val=x.val at hb
  exact hx (hb ▸ b.property)

private theorem ofSubgroups_right_out {F : Type*} [Group F]
    (P B Q : Subgroup F) (hP : B≤P) (hQ : B≤Q) (hgen : P⊔Q=⊤)
    (x : Q) (hx : x.val∉B) :
    (RankTwoAmalgam.FaithfulCompletion.ofSubgroups P B Q hP hQ hgen).right x ∉
      (RankTwoAmalgam.FaithfulCompletion.ofSubgroups P B Q hP hQ hgen).middle.range := by
  rintro ⟨b,hb⟩
  change b.val=x.val at hb
  exact hx (hb ▸ b.property)

include hm in
/-- Every compatible native amalgam automorphism has a marking-preserving extension. -/
theorem exists_native_action_extension
    (a : RankTwoAmalgam.Iso (nativeAmalgam m) (nativeAmalgam m)) :
    ∃ f : MulAut (ReeF4.Model m),
      (∀ x, f (x : ReeF4.Parabolics.parabolic m .linear).val=(a.left x).val) ∧
      (∀ x, f (x : ReeF4.Parabolics.parabolic m .suzuki).val=(a.right x).val) := by
  let c := modelCompletion m
  let d : Completion m (ReeF4.Model m) := c.comapIso a
  have hc := model_overlap m
  have hd : d.left.range ⊓ d.right.range = d.middle.range := by
    simpa only [d,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using hc
  have heO := pair_overlap c d hc
  apply exists_marked_pair_equiv c d hc hd
    (ReeF4.SmallCompletion.reflection m .linear) (ReeF4.SmallCompletion.reflection m .suzuki)
    (ReeF4.SmallCompletion.reflection_sq m .linear) (ReeF4.SmallCompletion.reflection_sq m .suzuki)
    ?_ ?_ (ReeF4.SmallCompletion.reflection_product_eight m) (iso_reflection_product_eight hm a)
    (Completion.cycle_length_ge_sixteen (c.pairCompletion d) hm heO)
    (Completion.nine_transitive (c.pairCompletion d) hm heO)
    (Completion.cycle_length_ge_sixteen c hm hc)
    (Completion.cycle_length_ge_sixteen d hm hd)
  · exact ofSubgroups_left_out
      (ReeF4.Parabolics.parabolic m .linear) (ReeF4.Parabolics.borel m)
      (ReeF4.Parabolics.parabolic m .suzuki)
      (ReeF4.Parabolics.borel_le_parabolic m .linear)
      (ReeF4.Parabolics.borel_le_parabolic m .suzuki)
      (by rw [sup_comm]; exact GreenBook.LieModels.ReeFour.parabolics_generate m)
      (ReeF4.SmallCompletion.reflection m .linear)
      (ReeF4.SmallCompletion.reflection_not_mem_borel m .linear)
  · exact ofSubgroups_right_out
      (ReeF4.Parabolics.parabolic m .linear) (ReeF4.Parabolics.borel m)
      (ReeF4.Parabolics.parabolic m .suzuki)
      (ReeF4.Parabolics.borel_le_parabolic m .linear)
      (ReeF4.Parabolics.borel_le_parabolic m .suzuki)
      (by rw [sup_comm]; exact GreenBook.LieModels.ReeFour.parabolics_generate m)
      (ReeF4.SmallCompletion.reflection m .suzuki)
      (ReeF4.SmallCompletion.reflection_not_mem_borel m .suzuki)

private theorem native_action_ext {f g : MulAut (ReeF4.Model m)}
    (hl : ∀ x : ReeF4.Parabolics.parabolic m .linear, f x.val=g x.val)
    (hr : ∀ x : ReeF4.Parabolics.parabolic m .suzuki, f x.val=g x.val) : f=g := by
  have h : ReeF4.Parabolics.parabolic m .linear ⊔ ReeF4.Parabolics.parabolic m .suzuki ≤
      f.toMonoidHom.eqLocus g.toMonoidHom := sup_le
        (fun x hx => hl ⟨x,hx⟩) (fun x hx => hr ⟨x,hx⟩)
  rw [sup_comm,GreenBook.LieModels.ReeFour.parabolics_generate] at h
  exact MulEquiv.ext (fun x => h (mem_top x))

/-- The unique native extension, with multiplication defined by its original
compatible parabolic restrictions. -/
def nativeActionExtension :
    RankTwoAmalgam.Iso (nativeAmalgam m) (nativeAmalgam m) →* MulAut (ReeF4.Model m) where
  toFun a := Classical.choose (exists_native_action_extension hm a)
  map_one' := by
    apply native_action_ext
    · intro x
      exact (Classical.choose_spec (exists_native_action_extension hm 1)).1 x
    · intro x
      exact (Classical.choose_spec (exists_native_action_extension hm 1)).2 x
  map_mul' a b := by
    apply native_action_ext
    · intro x
      rw [(Classical.choose_spec (exists_native_action_extension hm (a*b))).1]
      change (a.left (b.left x)).val =
        (Classical.choose (exists_native_action_extension hm a))
          ((Classical.choose (exists_native_action_extension hm b)) x.val)
      rw [(Classical.choose_spec (exists_native_action_extension hm b)).1,
        (Classical.choose_spec (exists_native_action_extension hm a)).1]
    · intro x
      rw [(Classical.choose_spec (exists_native_action_extension hm (a*b))).2]
      change (a.right (b.right x)).val =
        (Classical.choose (exists_native_action_extension hm a))
          ((Classical.choose (exists_native_action_extension hm b)) x.val)
      rw [(Classical.choose_spec (exists_native_action_extension hm b)).2,
        (Classical.choose_spec (exists_native_action_extension hm a)).2]

theorem nativeActionExtension_left
    (a : RankTwoAmalgam.Iso (nativeAmalgam m) (nativeAmalgam m))
    (x : ReeF4.Parabolics.parabolic m .linear) :
    nativeActionExtension hm a x.val=(a.left x).val :=
  (Classical.choose_spec (exists_native_action_extension hm a)).1 x

theorem nativeActionExtension_right
    (a : RankTwoAmalgam.Iso (nativeAmalgam m) (nativeAmalgam m))
    (x : ReeF4.Parabolics.parabolic m .suzuki) :
    nativeActionExtension hm a x.val=(a.right x).val :=
  (Classical.choose_spec (exists_native_action_extension hm a)).2 x

private theorem middle_of_left {F : Type*} [Group F]
    (P B Q : Subgroup F) (hP : B≤P) (hQ : B≤Q)
    (a : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B Q hP hQ)
      (RankTwoAmalgam.ofSubgroups P B Q hP hQ)) (f : MulAut F)
    (hl : ∀ x : P, f x.val=(a.left x).val) (x : B) :
    f x.val=(a.middle x).val :=
  (hl (inclusion hP x)).trans (congrArg (fun y : P => y.val) (a.left_commutes x))

theorem nativeActionExtension_middle
    (a : RankTwoAmalgam.Iso (nativeAmalgam m) (nativeAmalgam m))
    (x : ReeF4.Parabolics.borel m) :
    nativeActionExtension hm a x.val=(a.middle x).val :=
  middle_of_left (ReeF4.Parabolics.parabolic m .linear) (ReeF4.Parabolics.borel m)
    (ReeF4.Parabolics.parabolic m .suzuki)
    (ReeF4.Parabolics.borel_le_parabolic m .linear)
    (ReeF4.Parabolics.borel_le_parabolic m .suzuki)
    a (nativeActionExtension hm a) (nativeActionExtension_left hm a) x

theorem nativeActionExtension_injective : Function.Injective (nativeActionExtension hm) := by
  intro a b hab
  apply RankTwoAmalgam.Iso.ext
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun f : MulAut (ReeF4.Model m) => f x.val) hab
    rw [nativeActionExtension_left,nativeActionExtension_left] at h
    exact h
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun f : MulAut (ReeF4.Model m) => f x.val) hab
    rw [nativeActionExtension_middle,nativeActionExtension_middle] at h
    exact h
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun f : MulAut (ReeF4.Model m) => f x.val) hab
    rw [nativeActionExtension_right,nativeActionExtension_right] at h
    exact h
end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
