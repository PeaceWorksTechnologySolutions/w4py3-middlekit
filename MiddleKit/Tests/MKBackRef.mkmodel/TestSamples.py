def test(store):
    from Node import Node

    nodes = store.fetchObjectsOfClass(Node)
    for n in nodes:
        children = n.children()
        if children:
            children.sort(key=lambda c: c.serialNum)
            assert n.value() == ''.join([c.value() for c in children])
