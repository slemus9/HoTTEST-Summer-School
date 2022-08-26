# 🏗 Under construction 🚧

There are some nice implementations of categories around. In a move that serves little explicit purpose and conveniences no one, I asked myself: *can we implement categories without composition?* I.e., without taking composition as a primitive?

The motivation for this actually comes from an observation about associativity. Instead of demanding that $f \circ (g \circ h) = (f \circ g) \circ h$, we can instead demand that the $\text{Hom}$ operation is functorial: for all $c$ objects of $C$, and all $f,f'$ arrows of $C$:

$$ \text{Hom}_C(c,f \circ f') = \text{Hom}_C(c,f) \circ \text{Hom}_C(c,f') $$

This implies associativity.

It got me wondering: can we rephrase composition itself in terms of $\text{Hom}$? The answer is yes; but it quickly gets syntactically terrible, at least when sticking to conventional notation. Still, I wanted to see it through.

We'll make it just a little better by using the notation $C(-,-)$ instead of $\text{Hom}_C(-,-)$.

Here's how we start constructing our category:

A **category** $C$ is comprised of

* a set of objects $C_0$

* for any objects $a,b \in C_0$, a set $C(a,b)$

* for all $a \in C_0$, $1_a \in C(a,a)$.

* if $g \in C(a,a')$ and $f \in C(b,b')$, then $C(g,f) : C(a',b) \to C(a,b')$.

At this point, we have a couple of tasks—and a couple of choices. How do we implement

* associativity?

* the behavior of identities?

Technically, we're not allowing "mixed" applications of the hom-functor to objects and arrow, e.g. $C(a, f)$, so our associativity definition given at the beginning doesn't quite work. We have a couple options for how to proceed.

First, note that we can already tell what composition should be. Given objects $a,b,c \in C_0$ and arrows $g \in C(a,b)$, $f \in C(b,c)$, we have as a definition

$$ f \circ g \doteq C(g,f)(1_b) $$

where we've used the fact that $C(g,f) : C(b,b) \to C(a,c)$.

At this point we *could* just impose associativity as we typically do: given $a,b,c,d \in C_0$ and $g \in C(a,b), f \in C(b,c), h \in C(c,d)$,

$$ C(C(g,f)(1_b),h)(1_c) = C(g, C(f,h)(1_c))(1_b) $$

But wouldn't it be nice to bake functoriality into our axioms?

...What *is* functoriality in these terms, anyway? Maybe it looks a little different.

Let's talk a bit about what we're doing $C(g,f)$ represents the function that performs precomposition with $g$ and postcomposition with $f$ at the same time. 

(Hey, there's another definition of associativity: $C(g,f) = C(g,d^1f) \circ C(d^1g,f) = C(f,d^0g) \circ C(g, d^0f)$, using the (co)domain identity maps.)

A functor $F : C \to D$ satisfies $F(f\circ (-) \circ g) = Ff \circ F(-) \circ Fg$. In other words,

$$ F \circ C(g,f) = D(F g, F f) \circ F $$

(We allow ourselves composition in Set; however, we could just as well view Set as a category of this new sort and use the same notation.)

A contravariant functor would flip the arguments to $C$.

We also have

$$F(1_a) = 1_{F a}$$

which is a law we'll leave unchanged.

So for $C$ to be a functor—or, here, a mixed-variance bifunctor?—we need to look at how it composes with...itself. It has two arguments, so let's do them one at a time. The right one:

$$ C(h, -) \circ C(g, f) = \text{Set}(C(h, g), C(h, f)) \circ C(h, -) $$

The left one:

$$ C(-, h) \circ C(g, f) = \text{Set}(C(f, h), C(, h)) \circ C(-, h) $$

...Wait, what exactly going on here with $\text{Set}$? Well, $C(h, g)$ and $C(h, f)$ are both arrows in $\text{Set}$—functions—and $\text{Set}(C(h, g), C(h, f))$ is a map from functions between sets to functions between sets.

Combining them (remember how I said the syntax would get spiky?):

$$ C \circ C(g,f) \times C(g',f') = \text{Set}(C(f,g'),C(g,f')) \circ C $$

Let's give ourselves a little more faith that this is correct with a diagram.

[!!|Need to insert the diagram here.]

(Aside: You know, we often rely on products for composition of functions with more than one argument. It doesn't need to be this way! When dealing with curried functions, we could define `_∘∘__ : {A B C A' B' : Type} → (A → B → C) → (A' → A) → (B' → B) → (A' → B' → C)` by `f ∘∘ g h = λ a → λ b → f (g a) (h b)`. It's a fairly common situation but we don't have a good syntax for it.)

The identity condition for functors becomes

$$ C(1_a, 1_b) = 1_{C(a,b)} $$

where $1_{C(a,b)}$ is the identity function on $C(a,b)$ in $\text{Set}$.

Is this enough? Does this automatically give us the correct behavior on identities?

Let's see if we can compute. We should be able to evaluate $C(f,1_a)(1_a)$ and get $f$...but as far as I can see, we can't. Our current rules don't seem to give us a way to shuffle an evaluated-on thing into an argument position. Unless they do... Perhaps we need another basic rule.

If we view Set as a category in the way we're viewing $C$ as a category, then what is function evaluation? It's a bit tricky: objects in a category aren't types, and have no notion of being "inhabited", much less enjoying function semantics. But we *do* have the quite degenerate notion that $f:a \to b$ somehow "sends" $a$ to $b$: in some sense, we might hope to say $f(a) = b$. See where I'm going with this?

Well, maybe not, because there are at least two places I could be going with this. One: we establish a sort of "structure preserving semantics" that Set enjoys and which translates this degenerate thing into something that "looks like it", but a type-degree lower. Two: we look at the category of elements, and try to bake that into the notion of Set (and into the notion of any category over which we might hope to enrich).

I really like the idea of being able to compute with certain semantics, though, and that the semantics for Set might be different than for a category enriched in some other category. Being able to introduce that extra equipment sounds cool.

Let's also note that we use that relationship between type and inhabitant—generally, where we introducing data within something—to define other parts of categories as well (the objects and hom-sets). We're using the semantics of Set to put these axioms in place. So, what is a semantics in the first place?

The whole notion of a type is: you can have an element of it. That is, for $A\text{ type}$, you can form $x : A$. And where do we put this judgment, when it is some unspecified $x$? In the context. And a context serves as a variable binding for expressions, just like a function; functions and function types internalize contexts. Positing an element of a set is inseparable from—or at least goes hand-in-hand with—forming a function out of it.

But we're being kind of circular, because we're asking what it means to "be a" Set or type in the first place, which is a content-filling relation similar to what we're trying to describe in the first place. But they're all united under a single thing, which is different than having multiple things which things can be under.

Something about...finding a language in which do describe the process of specifying semantics for something...for specifying the process of how to practice with that thing...and then preserving the structure of that in certain ways...

In any case, I wonder if $C(f,1_b)(1_b)$ can be computed by somehow generalizing the transition from $b$ to $1_b$...and by somehow transforming the judgment $f : C(a,b)$ in the first place...and by forming an analogy between $C$ and $\to$, and by considering $C(f,1_b) : C(b,b) \to C(a,b)$.

## Thoughts about other possible approaches

But, what's the point?

Well, one hope is that this will let us generalize to higher categories easily. But it doesn't feel like it...we don't get that same sort of "infinite amount of data" we get from path induction, for example.

Hey, what about using comma categories? And phrasing things in terms of that sort of relationship among probes? Maybe comma categories should be the fundamental things. Notice the similarity in the shape to the domain/codomain map definition of a category internal to another category.

It just seems kind of awkward to constantly be talking about a pair of arrows. Should we view them as one object instead, and use projections and other operations to piece them together, reverse them, and swap components?

It would be great to be able to mix levels and use things like $C(c,f)$. I mean, that's one of the most convenient parts. And then there's the fact that we can piece these together coherently to get something like $C(g,f)$. Maybe we can talk about $C(-,-)$ as the kind of thing that pieces together coherently over levels like that?

Or maybe the $C(-,-)$ thing is artificial. Why *two*? Or...maybe the twoness should be more fundamental, and something like $C(-,-)$ should emerge as a consequence of that twoness being constructible everywhere.

On the other hand, the definition of functoriality seems very close to the definition of naturality. I wonder if we can realize natural transformations as formally functors between functors that irrelevantize some piece of data that 1-categories don't have.

Here's another idea: dualize the above construction with respect to function application. That is, if $f \in C(b,b')$, look at $\text{ev}_f : C(a,b) \times C(b',c) \to C(a,c)$.

But staring at that, it occurs to me...remember how $\circ$ actually takes three object arguments, as $\circ_{a,b,c}$? Well, $\text{ev}_f$ is basically replacing that middle $b$ with $f$. If we instead view the middle one as an arrow argument, then $f \circ_{a,-,c} g = C(g,f)$. Keeping the objects implicit, $f \circ (-) \circ g = C(g,f)$ Also, we can replace the outer two objects $a,c$ with arrows as well to get an operation that composes *five* arrows.

Wait, what?! Why would we want that? Well...we don't, but it does show something interesting: that even the most fundamental operations can accommodate this kind of "level-jumping" where we're able to turn objects into arrows. The fact that $\circ_{a,-,c}$ turns into $\circ (-) \circ$ is also interesting.

We're kind of cheating with $\circ (-) \circ$, by the way. We can only omit parentheses if we also omit the object arguments, as these object arguments would change depending on the parenthesization.

One nice thing about $C(g,f)$ is that it doesn't require any extra polymorphism. $\text{ev}_f$ should actually be something like $\text{ev}^{a,c}_f$ to account for the domain and codomain of the precomposed and postcomposed arrows, respectively. But the type of $C(g,f)$ is determined entirely by the types of $f$ and $g$. The annoying thing is that the "duality" rules where $g$ is treated contravariantly seem to come out of nowhere.

Hey, are we able to use the above identity on objects too? Part of the problem is that C(g,f)(a) only sort of makes sense; we need to lift a to the level of an arrow. But we can do that if we want.

In general, any categorical law is compatible with replacing objects $a$ with arrows $1_a$ for a certain vague sense of "compatible".

## Anyway, let's write some Agda code

So what does this look like in Agda? Let's define 
